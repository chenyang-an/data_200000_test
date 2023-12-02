variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175090048735682093177843065940 : ((p3 ∧ (p4 ∧ ((((p2 ∧ False) → False) ∧ ((p4 ∨ p4) ∨ p2)) ∧ (True ∨ p2)))) → ((p3 → p4) ∧ (p2 → (p3 ∧ (p5 ∨ (p5 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- Implications on the right can always be decomposed.
  intro h21
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h38 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h22
  -- Conjunctions on the left can always be decomposed.
  let h40 := h1.left
  let h41 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h41.left
  let h43 := h41.right
  -- Conjunctions on the left can always be decomposed.
  let h44 := h43.left
  let h45 := h43.right
  -- Conjunctions on the left can always be decomposed.
  let h46 := h44.left
  let h47 := h44.right
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h48 =>
    -- Disjunctions on the left can always be decomposed.
    cases h48
    case inl h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h50 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h51 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h53 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h54 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h56 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h57 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635154383965026437872252043452 : ((((((False → (True ∧ True)) → ((((p5 ∧ ((True ∨ (p2 ∨ (True ∨ True))) ∨ p1)) ∨ True) → False) ∨ p4)) → ((p1 ∨ p4) ∧ p2)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78864346030989803182785949047 : ((((True ∧ True) ∧ ((False ∨ (p4 → p5)) ∧ (((((False → p1) → p2) → True) ∧ p2) ∧ (p4 ∨ ((p4 ∨ p4) ∨ False))))) ∧ (p2 → p2)) → p5) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h16 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h18 := h11 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h22 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h23 := h11 h22
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h25 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h26 := h11 h25
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112136050923771740282262667509 : (((False ∧ ((False ∨ p2) ∨ ((((p2 ∨ p1) ∨ p5) ∧ p5) → (((p2 → (True ∧ ((p2 ∧ True) → p2))) ∨ p2) → False)))) ∨ True) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53442317771413035916097145989 : (((((False → True) ∧ p2) ∨ (p1 ∧ ((p4 → (True ∧ p3)) ∧ p1))) → ((((p2 ∨ (p3 ∨ True)) ∨ ((p2 ∨ p1) ∨ p3)) → p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352624382662954244281370540068 : (p4 → ((True ∧ p3) ∨ ((((p2 ∨ ((((False → True) → (p4 ∨ (p1 → p3))) ∨ ((p1 ∧ (True ∨ True)) ∧ True)) → True)) ∨ p3) → p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190095431560195764974581733653 : (((((True ∨ p2) → (p2 → p5)) ∨ (p1 ∨ p4)) ∧ p2) ∨ ((p3 ∨ ((False → p4) ∧ ((((False → True) ∨ False) → p2) ∨ True))) ∨ (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615238746646125785367930331831 : (((((p1 ∨ ((((p4 → (p3 ∨ p1)) ∨ p5) ∨ (p1 ∨ ((p3 → p2) ∧ p3))) ∨ p5)) ∧ ((((p4 ∨ False) ∧ True) ∨ False) → p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244215715991865415889077557515 : ((True ∧ p5) ∨ ((((p2 → p1) ∨ False) ∧ (False → p2)) → ((p4 ∧ (p1 ∧ ((True ∨ p3) ∧ (p5 ∧ (p5 ∧ (p4 ∧ (p3 ∧ p5))))))) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318630110786283193193749885124 : (p4 ∨ ((p1 ∧ (((p3 ∧ ((False ∧ p5) ∨ ((p2 ∨ p2) ∨ (p1 → (p1 → (True → (p3 ∧ (True ∨ True)))))))) → p4) → p4)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640677051415747125747792563767 : (((((p3 ∨ p5) ∧ (True ∧ ((False ∨ p3) → ((((p3 ∧ (p1 ∧ True)) → False) → True) ∨ ((p3 ∧ p1) ∨ (p1 ∨ (p1 → True))))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191015019283171983258533693167 : (((p5 ∨ (p1 ∧ (p5 ∧ True))) ∨ (p1 → (p5 ∧ p5))) ∨ (False → (((p3 → p5) → ((p4 ∧ False) ∧ ((p1 → (p5 → True)) ∧ p4))) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186101536766434318625061321240 : (((((p5 ∨ ((p2 ∨ p2) ∧ p5)) ∨ p5) ∨ (p5 → p2)) ∨ True) → (((False ∨ ((p4 ∨ (p5 ∧ p5)) ∧ p1)) ∧ (p1 → p5)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
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
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53796212932002994459971742431 : ((((((p1 → p3) ∨ (False ∨ p5)) ∧ (p5 ∨ True)) → False) ∨ (True ∨ ((p3 ∧ ((p5 → (False ∧ (p5 ∧ p4))) ∨ p5)) → (False ∨ p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238775182287644109228610734000 : ((p1 ∨ True) ∧ (p4 → ((((((p1 → p2) → p2) ∧ p2) ∨ (p1 → (((False → p1) → False) → (True ∧ (p1 ∨ p3))))) → p1) ∨ (p4 ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117420661260183233388148269798 : ((p1 ∧ ((((p3 → p2) ∨ p1) ∨ (p4 → (p1 → (((p4 → p5) → p2) ∨ (True ∧ ((p4 ∧ True) → p3)))))) → (p3 ∨ p5))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258799956907748538518086873078 : ((True → False) → ((True → False) → ((False ∧ True) ∧ ((p5 ∨ p5) ∨ ((((p3 ∧ p4) ∨ p5) ∨ ((p3 ∧ p3) ∨ (p2 → False))) ∨ (True ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754445751204870338336732689428 : (((False ∧ ((p5 → p1) → ((((p3 ∧ (((p4 ∨ (p5 ∨ p3)) ∨ p5) ∨ ((p4 → (False → (p4 → True))) → False))) → p4) → p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181462380027541288748333471574 : ((p4 ∨ ((p3 ∨ (((p2 → (False ∧ (p5 ∨ p1))) ∨ p4) → p4)) ∨ p3)) → (p4 → (((True ∨ p1) ∨ False) → ((True ∧ (p2 ∧ p1)) ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314022278225156124287107155157 : (p3 ∨ ((p3 ∨ (p3 ∨ (False ∨ (p3 ∧ ((True → ((((True → False) ∨ p1) ∧ ((False ∧ (p1 ∧ False)) ∧ False)) → p1)) → p4))))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345334020018865197688098753271 : (p3 → ((((p1 ∧ ((p5 → p3) ∧ p3)) ∧ ((p5 ∨ p1) ∧ ((p3 → (((True ∧ True) → p3) ∧ (p4 ∨ p3))) → (p2 → p5)))) ∧ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615982354691562049673996605903 : ((((((((True → (p1 ∨ p5)) → p5) ∨ ((p1 ∧ p4) ∨ p5)) ∧ (True → p5)) → (((p2 → p4) → (p2 ∨ False)) ∧ (p2 ∨ True))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52255338212862992064283775553 : (((p2 ∨ (((((p3 ∧ False) ∨ p4) ∨ p5) ∨ (p1 ∧ (p2 ∨ p4))) ∧ (p1 ∨ p1))) → ((True → p5) → ((p3 ∨ (False → p5)) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- False on the left can always be used.
            apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- False on the left can always be used.
          apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208028286002473370559204469792 : (((True ∧ (True → p3)) ∨ (p3 → p4)) → ((p3 ∨ ((True → ((p4 ∨ (p3 ∧ (False → True))) ∧ p3)) ∨ (((p3 ∧ p5) → p4) ∨ p5))) ∨ p2)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157515762950471032260932043436 : (((p1 ∨ ((p2 ∨ (p3 ∧ p3)) → ((((p4 → p3) → True) ∨ p5) → (False ∧ False)))) ∨ (False → False)) ∨ (((p2 ∧ p3) ∨ (False → True)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226182486591180634513052286992 : (((p1 ∨ p4) ∨ p2) ∨ ((p2 ∧ (True → ((False → p2) ∧ p3))) → (((p5 ∨ (p2 ∨ (p3 ∨ (p4 ∨ (p3 ∧ (p4 ∧ p1)))))) ∨ p4) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234098472874594028470800786866 : ((True → (p5 ∧ False)) → (p2 ∨ ((p3 ∧ ((p4 ∨ p4) → p2)) ∧ (((p5 ∧ False) ∨ p3) ∨ ((((p4 → False) ∨ p3) ∨ (p4 ∧ p2)) ∨ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193847494004942888891430160441 : ((True ∨ ((p4 ∧ ((p1 ∧ p5) ∨ p3)) ∧ (True → True))) → ((p1 → False) ∨ ((True ∧ (p5 ∧ p4)) → (((p3 → True) ∧ (p4 ∨ p2)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h25
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134274612270645997101933628266 : ((((p3 ∨ p5) ∧ ((((p3 ∨ (((p5 ∧ (p2 ∧ (p2 → (p1 → p1)))) ∨ p4) ∧ p2)) ∨ p3) ∨ p1) → p4)) ∨ True) ∨ (p1 → (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69112859579220349029508176456 : ((p5 → (((((False ∧ (p2 ∧ p3)) ∨ False) ∧ ((((((True ∧ False) ∨ True) ∧ p3) ∨ p2) → False) → (p4 ∨ p5))) ∨ False) ∨ (p5 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234464429398917008285872616259 : ((p2 → (False ∨ p1)) → ((p3 → ((p1 ∧ (((True ∧ False) ∧ True) ∧ (p2 ∧ (p4 ∨ p2)))) ∧ (p2 → p3))) ∨ ((False ∧ p1) → (p3 ∨ p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352470684049529065790258221038 : (p4 → ((True ∧ (p2 ∨ True)) → ((p2 → ((p3 → ((p5 ∧ False) ∨ ((p5 ∧ p1) ∨ p4))) ∨ (p1 → p4))) ∨ ((p3 → (p5 ∧ p5)) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136315058679505436284442706118 : ((((p5 ∨ (p2 → p3)) ∨ True) ∧ (((p5 ∨ p5) ∧ (p4 ∧ p4)) ∧ ((p4 → (p3 ∧ p4)) ∨ (False ∧ (p3 ∧ p3))))) ∨ (p4 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147406685696998193180435465661 : ((((((p1 → p2) ∧ False) ∧ p1) ∧ (((p3 ∧ (True → p4)) ∧ (False ∨ (p4 ∨ p3))) ∧ (p3 → False))) ∨ True) ∨ (p2 → ((p5 → True) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804340254064082334389177750685 : (((p3 → ((((p5 ∧ ((p4 ∨ p4) ∧ p4)) ∧ (p5 → p4)) ∨ (p1 → False)) ∨ ((((p4 ∧ (p2 ∧ p2)) ∧ p5) → (p5 ∨ False)) → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255118991537899631160702961151 : ((p4 ∧ p3) → (((((((p1 ∨ ((p2 ∨ (p4 ∨ p4)) ∧ True)) ∨ p5) ∧ (False ∧ p3)) ∧ (False ∨ ((p4 ∨ p2) ∧ True))) ∧ p5) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_49166552279951067813561856317 : (((((p5 → p3) ∧ (False ∨ (p2 ∨ p5))) ∨ (((p2 → p2) → p4) → (((p2 ∧ (p2 → False)) → p5) ∧ True))) ∨ (p1 ∨ (True ∨ False))) ∨ p2) := by
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
theorem thm_5_vars_638466626476622343133595216873 : ((((((p4 → ((p2 → False) → p5)) ∧ p1) ∨ ((((True → (p4 ∨ (p3 ∧ False))) ∨ p4) ∧ (False → (p1 → True))) → (p4 ∨ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141470279259520566251542191470 : (((p4 ∧ (p2 ∧ True)) ∧ ((p2 → (((p3 → p4) ∨ p1) ∨ ((p1 ∧ p4) ∧ ((p5 ∧ (p3 ∧ p5)) ∨ p3)))) ∨ True)) → ((True → False) → False)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655509139358266418385873979420 : (((((((p2 → ((p4 ∨ p3) ∧ (p5 → (p4 ∨ p5)))) → ((p2 ∨ p1) → (p3 ∨ (p2 ∧ p5)))) ∨ p4) → (p2 → p4)) ∨ (False → p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_50079737823015983896472485064 : (((False ∧ ((((p2 ∨ (((p4 ∨ p4) ∨ (p5 → False)) ∧ p1)) ∨ (p4 ∨ (p1 ∨ True))) ∧ p1) ∧ p2)) ∧ ((True ∨ (p4 ∧ p5)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740875859320411573371538585422 : ((((p3 ∨ p1) ∨ ((p3 ∨ (p3 → ((p2 ∧ p1) ∨ (p2 → (True ∧ (p5 ∨ (True → ((p5 → p4) ∨ p2)))))))) ∨ (p5 ∧ (True ∧ p4)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45894320551583913952326402423 : (((p3 → (p5 → (False ∧ ((((((True → p2) ∨ (p2 ∧ p2)) → (p3 → p5)) ∨ ((False ∧ (p3 ∨ p4)) ∧ p2)) ∨ p5) ∧ False)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138894097383869954667554167639 : (((True → (p1 ∨ ((p2 ∧ (((p3 ∧ p1) → True) → (p1 → p4))) ∧ (p2 → ((True → p5) → (False ∨ p2)))))) ∧ p4) → ((p5 ∨ p2) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161545655372690936721822903167 : ((p5 ∧ ((p4 → ((True ∧ p5) → True)) ∧ ((p3 ∧ p1) ∧ ((p5 ∧ (p3 ∧ (p3 ∧ p1))) ∨ False)))) → (p4 ∨ (((p3 → p2) → False) ∨ p5))) := by
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
  cases h7
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184273859689889716446711531449 : (((((p3 ∨ p4) ∨ (p1 ∧ (p5 ∧ False))) → (p5 → False)) → p1) ∨ ((p4 ∧ (p2 ∨ (False → p4))) ∨ ((((p1 ∧ p4) ∨ True) ∨ p2) ∨ p5))) := by
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
theorem thm_5_vars_64748198801813368800887619929 : ((p2 ∨ (((p1 ∨ ((((p3 ∧ False) ∨ p4) → ((p4 → False) → (p1 ∧ (p5 → p2)))) ∧ p3)) → (p2 ∧ (p5 ∧ (p5 ∨ p4)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44067529278103023170970972743 : (((((p5 ∨ (p5 ∨ (True ∨ ((p4 ∧ ((False ∧ (True ∧ (p1 → p5))) ∧ False)) ∧ (p2 → p1))))) → p1) ∧ ((p3 ∨ p1) → p5)) → p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p5 ∨ (True ∨ ((p4 ∧ ((False ∧ (True ∧ (p1 → p5))) ∧ False)) ∧ (p2 → p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674673635006252892056586996155 : ((((p1 → (p1 ∨ (((((p2 → p5) → False) ∧ True) → (p5 → (p2 ∨ (((p5 → True) ∧ p1) → p5)))) ∧ p3))) → ((p3 ∧ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52456507196883615374736251120 : (((p5 ∧ (False ∧ ((p2 ∧ (p5 ∨ (p2 ∧ p3))) → ((p2 ∨ False) → p3)))) ∧ (((p1 ∧ (p1 → True)) ∧ ((p1 ∨ False) ∨ p1)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121390087657563584676751617355 : (((((((False ∧ p5) ∧ ((p4 → (p5 ∨ p2)) ∨ p4)) ∨ False) ∧ (((p4 → False) ∧ (p4 → p2)) ∧ (False ∧ True))) ∨ True) → False) → (p5 → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((False ∧ p5) ∧ ((p4 → (p5 ∨ p2)) ∨ p4)) ∨ False) ∧ (((p4 → False) ∧ (p4 → p2)) ∧ (False ∧ True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232270745543292956328618854509 : (((p2 → p2) → False) → ((p2 → ((p1 → p5) ∧ p1)) → (((p3 → (p2 ∧ (((p5 → True) ∧ p2) → False))) → ((p5 ∧ p3) ∧ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168656950264323072114937844081 : ((p4 ∧ (True ∨ ((p4 → ((p4 ∨ False) ∨ ((p3 ∧ p2) ∧ (p2 ∧ p5)))) → (False ∨ True)))) → ((p2 ∨ (p3 → p2)) ∨ (p2 → (p4 → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317901512798174613285271414302 : (p4 ∨ ((p2 ∧ (p2 ∧ ((p4 → (p4 → (True ∨ p5))) → (((p4 ∨ p5) ∨ True) → (p1 ∧ (p4 ∧ (p5 ∨ ((p5 ∨ p5) → False)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164871575425538605621570294749 : (((p5 ∨ ((p3 ∧ True) ∨ ((p2 ∨ (True ∨ (p1 ∧ True))) → ((p5 ∨ p1) ∧ p3)))) ∨ True) ∨ (p5 ∧ (((p2 ∨ True) ∨ (p2 ∧ p4)) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215188369090871965084360718283 : ((True ∧ (p1 ∧ (p4 → p5))) ∨ ((((p3 ∨ (p4 ∧ (p2 → ((p3 → p3) ∨ ((p3 → p2) ∧ p1))))) → p1) ∨ ((p1 ∧ p2) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158789006491090216568942552180 : ((p5 ∧ (((p2 ∧ (((((False ∨ p5) ∧ p4) ∧ p5) ∨ (True → p4)) → False)) ∨ p5) ∧ (p3 → p3))) ∨ (p4 → ((p4 → True) ∧ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186123526843715027245061125576 : ((((p1 ∧ (True → (p4 → True))) ∨ ((False ∨ p4) ∧ True)) ∨ p3) → ((p5 ∨ ((True ∨ False) ∨ (False → p2))) ∧ (p3 → (p4 ∨ (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130259792326738318639563236649 : ((((p2 ∨ (False ∨ (False ∨ (((p2 ∨ (p4 ∧ p5)) ∨ p2) → True)))) → ((p1 ∧ (p1 → p2)) ∧ False)) → (p5 → False)) ∧ (p4 ∨ (p5 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ (False ∨ (False ∨ (((p2 ∨ (p4 ∧ p5)) ∨ p2) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141538858519604224992973212630 : (((False ∧ (True → False)) ∨ ((p3 ∧ (p4 ∧ ((p2 ∧ (p2 ∧ (p4 ∨ (p4 ∨ ((False → p2) ∧ p3))))) ∧ p4))) → p1)) → ((p3 → p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777429282394589744629981049884 : (((p1 ∨ (((p4 ∧ p3) ∨ ((True ∨ True) ∧ ((p5 ∨ (p1 → (p1 → p3))) ∨ (p3 ∨ p3)))) ∨ ((((p5 ∨ True) → p2) → p4) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683667800748222577211418109028 : ((((((p1 → p2) ∧ (p4 ∧ (((False ∨ (p5 ∧ p4)) ∧ p2) ∨ (p3 ∧ (False → p1))))) ∧ p4) ∨ (((p4 ∧ p4) ∨ False) → (True ∨ False))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136678973506371185089785680204 : (((False → (True → p3)) → (((p1 ∧ (p2 ∨ (p5 → False))) ∨ (p1 ∨ (p3 → (p5 ∨ (p1 → (True ∧ True)))))) ∨ p2)) ∨ ((False ∧ p4) ∧ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54820618727528412325884065875 : (((True → ((p2 → (True ∨ (False ∧ p3))) ∧ True)) → ((p2 ∧ ((p4 ∨ p4) → ((False ∧ p4) → (True → True)))) ∧ ((p3 → p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55430899147205805228992985376 : ((((p5 → (p3 ∨ (p1 → p1))) ∨ p2) → ((p2 → (True ∧ (p4 ∨ p5))) → (((p5 ∨ (p1 → (p2 → (True ∧ p1)))) ∧ p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115472834616088538218604742146 : (((p4 ∨ ((p1 ∨ (p4 ∨ (True ∧ p4))) ∨ False)) ∨ (p1 ∨ ((p4 ∨ True) ∨ (((p4 ∨ p5) ∨ True) → (p2 → (p4 ∨ False)))))) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68441072844568250789940256153 : ((p3 → (True ∧ ((((((p3 → ((True → (((p4 ∧ False) ∨ True) ∧ True)) ∧ p2)) ∧ p1) → p3) ∨ p3) → p1) ∨ ((p5 ∧ False) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40959255149431187465262909357 : ((((((True ∨ (p5 ∧ ((p3 ∧ False) → True))) ∨ ((p4 ∧ (p2 ∨ p5)) ∨ p5)) → (p3 ∧ (p5 → (p5 → p2)))) ∨ (p2 ∨ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691433433580041566574810742463 : (((((p1 ∧ p3) ∨ ((p4 ∨ ((True → p3) → p5)) ∨ ((True → False) ∨ (p1 → p5)))) → ((p3 → ((True → (False ∧ False)) ∧ p1)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53810562023093658999926159107 : ((((p5 → (True → (((True ∧ p4) ∧ False) ∧ False))) → p5) ∨ (p2 ∨ ((True ∨ (p4 ∨ (((p2 → (p4 ∨ True)) ∨ p4) → True))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60794679458248567497373578206 : ((True ∧ (False ∧ (((((p5 → (p4 ∨ p4)) → p5) → ((((p2 ∧ True) → p1) ∧ p5) → p4)) ∧ (True → p5)) ∧ (p1 ∧ (p5 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233883566663114657705808283480 : ((p4 ∨ (p2 ∨ True)) → ((p5 → ((p1 ∧ (((p2 ∨ p5) ∨ ((p3 ∨ True) ∧ (True → p1))) ∧ p4)) ∨ ((p3 → True) ∨ p3))) ∨ (p5 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48422358384230510828706732811 : (((p3 → (((((False → ((p1 ∨ True) ∧ (p1 ∧ p1))) ∧ (True ∧ True)) ∧ ((p3 → False) → False)) → (True → False)) → p5)) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109706336057515965954015281820 : ((p4 ∨ ((p4 ∧ (p4 → p2)) ∨ (((p4 ∨ ((p4 ∧ ((False ∧ p2) → ((p1 ∧ p1) ∧ False))) ∨ p3)) ∨ p3) ∨ (True ∨ p3)))) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215029593615952485657368061974 : (((p2 ∨ True) → (p1 ∧ False)) ∨ ((((((p2 ∧ ((True ∧ ((p2 ∧ True) ∧ p4)) ∨ p3)) ∨ p2) → p1) → False) ∧ (p5 ∧ (p3 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158680416250597153842497289127 : ((p2 ∧ ((p2 ∨ (p4 ∨ ((p1 → ((p1 ∧ False) ∧ p4)) → (False → p1)))) ∧ ((p5 ∨ True) ∨ True))) ∨ ((p1 ∨ (True → p4)) → (p1 ∨ True))) := by
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
theorem thm_5_vars_57340067978950689577274025830 : (((p2 ∧ (p1 ∧ False)) ∨ (((p3 ∧ (p1 → ((p3 ∨ (p5 → p5)) → (True → (False ∧ False))))) ∨ (False ∧ p2)) ∨ (p2 ∧ (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202668414756891034319803863966 : (((False ∧ (p3 → p2)) → (p5 ∧ p4)) ∧ ((p2 ∨ (p2 ∧ (True ∧ (p4 ∧ (p2 → (p4 → p2)))))) → (True ∧ (p5 → ((p2 ∧ p1) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708202753034650222619239232165 : ((((p2 → ((p1 → (True ∨ p5)) → (p3 ∨ p1))) ∨ (((p1 → ((p4 ∨ p1) ∧ (False ∨ (p3 ∨ (True ∧ True))))) ∨ (p3 → p3)) ∨ p4)) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149987004983451584756925310771 : ((p4 ∨ (p1 ∧ ((((False ∨ True) ∧ p2) ∧ (p5 → (p1 ∨ (p2 ∧ p5)))) ∧ ((p2 ∧ p5) ∨ (p4 ∨ p3))))) ∨ ((False ∧ p5) → (p4 ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158471346226180612403993968147 : (((p4 → False) ∨ ((p3 ∧ ((((False ∨ (p2 ∧ p4)) ∧ p5) ∨ ((p5 → True) → p4)) ∧ p4)) ∧ p4)) ∨ (p1 → (p5 ∨ (p4 → (p4 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62349655216274188949268659339 : ((p3 ∧ ((p5 ∨ (p5 ∨ ((((((p3 → False) ∨ p3) → (True ∧ p1)) → (p3 → (p4 ∧ p3))) → p2) ∨ p5))) → (True ∧ (p2 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193992222905124571862830779484 : ((p3 ∨ (p1 ∨ (True ∧ (False ∨ (p3 → (p3 ∨ False)))))) → ((False ∧ (p4 ∧ ((p5 ∨ (True ∧ (p5 ∧ p5))) ∧ (True ∧ p2)))) ∨ (False → p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135613874238749356545850019281 : (((False ∨ ((((True ∧ p3) ∧ ((p2 → (p5 ∧ False)) ∨ (p2 ∨ p1))) ∨ p3) → False)) ∨ ((p2 ∧ p2) ∨ (True ∨ p1))) ∨ ((p3 → False) → p1)) := by
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
theorem thm_5_vars_55861927355097870963042364173 : (((p4 ∧ (True ∨ (p3 ∧ True))) ∧ (((False ∧ (p1 ∨ False)) → ((((False → p4) → p4) ∨ p1) → ((p5 ∨ True) → (p5 ∧ p3)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61205153296181367267926518331 : ((False ∧ ((True ∨ p4) → (((((p1 ∨ ((False ∨ p5) → (p4 ∧ False))) → ((p4 ∨ p2) ∨ (p1 ∧ (False ∧ p2)))) ∧ p2) ∧ False) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659804562358272389510773214950 : (((((p1 ∨ (((False ∧ p1) → (True ∨ (p4 ∧ (p4 ∧ p4)))) ∧ ((p5 ∧ (p2 → p1)) → (False ∧ (True → p3))))) ∧ p3) → (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53385978543905498906933567371 : ((((p1 ∧ ((((p2 → p4) ∨ (False ∧ False)) ∨ False) ∨ p5)) → True) → (((True ∧ p5) ∨ ((p5 ∨ (p2 ∧ p2)) ∨ (True ∧ p2))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137088120646835136393999372116 : ((True ∧ (((True ∧ (p1 ∧ ((False → (p3 → (p3 ∧ (p1 ∨ p1)))) ∧ ((p2 → p3) → (True → p2))))) ∨ p3) ∨ True)) ∨ ((True ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44288542918921494941941982971 : (((((p3 ∨ ((p2 ∨ (True → (p1 ∧ p4))) ∧ ((True ∨ p4) → p3))) ∨ (p5 ∧ p5)) ∧ ((p5 → p3) ∨ ((p5 → p4) → p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207820481170235829165815877568 : (((p4 → ((p4 → p5) → p2)) → False) → ((p5 ∧ (p2 ∧ p5)) → (((p2 ∨ (p1 → p5)) ∧ p4) ∨ (p2 ∨ ((p5 → True) → (p4 → p4)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67958406438216234078015021700 : ((p2 → ((((False → p1) ∨ p5) ∨ p1) → (p1 → (((False ∧ p4) ∨ p2) ∨ ((p4 → (p1 ∧ p1)) → ((True ∧ p5) ∨ (p1 → p1))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746583698545480614880310847493 : ((((p3 ∨ True) → ((((p1 ∧ (p3 ∨ p1)) ∨ (p4 ∨ p4)) ∧ ((((p4 → p4) → p1) → (False → False)) → False)) → ((True ∧ p3) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h14 : (((p4 → p4) → p1) → (False → False)) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h14
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : (((p4 → p4) → p1) → (False → False)) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h22
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h29 : (((p4 → p4) → p1) → (False → False)) := by
          -- Implications on the right can always be decomposed.
          intro h30
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h29
        -- False on the left can always be used.
        apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766689179241450752973383597795 : (((p4 ∧ (False ∨ ((p5 ∨ ((True ∧ True) ∧ p1)) ∨ ((True ∨ p2) → ((p1 ∨ (p5 → (p2 → (False → ((p1 → p3) ∧ p4))))) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40989599843481633793978399241 : ((((False ∨ ((p2 → (True → ((p1 ∧ p1) ∧ (p3 → p3)))) ∨ ((p5 ∧ (False ∧ (p1 ∧ (p1 ∨ p3)))) ∧ p5))) ∨ (True ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209022759398459954116004531530 : ((False ∨ (p5 ∧ (p3 → (p5 ∧ p5)))) → (p4 ∨ (True ∧ ((((((False ∨ p5) ∨ p3) ∨ (p2 ∨ p4)) → p3) ∧ p2) ∨ ((p5 ∧ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258764212020815414635896011485 : ((True → False) → (((p2 ∧ (p2 → (False → (((True ∧ ((((p5 → True) ∨ (p1 → True)) ∨ p4) ∨ p5)) ∧ p2) ∨ p3)))) → (p4 → False)) ∨ p3)) := by
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
theorem thm_5_vars_112445242844244195354281390661 : (((((((p2 ∧ p1) → True) → ((False ∨ (p3 ∧ ((((p1 ∨ p3) ∨ p1) → False) ∨ p4))) ∧ (p2 → p2))) → p1) ∨ p5) → p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246520498408079559087227573384 : ((p5 ∧ p1) ∨ ((((False → (p4 → p3)) ∨ ((False ∨ p1) → False)) ∨ True) → ((((p3 → (p5 ∧ p2)) ∧ ((p5 ∨ p5) → p5)) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_310626226916537468622416802875 : (p2 ∨ (((p3 ∧ p3) ∨ (p1 ∧ p2)) ∨ (p2 → ((((False → (p1 ∨ p5)) ∧ p3) ∧ (p5 ∧ ((((False ∧ False) → p1) → True) ∧ p2))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h7



