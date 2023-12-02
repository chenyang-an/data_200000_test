variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310066702508285175951249718328 : (p2 ∨ (((p3 → (True → p4)) ∨ ((((False ∧ False) ∧ (False ∨ True)) → True) ∧ (p5 ∧ p3))) → (p4 → (((True → p4) ∧ (True ∨ False)) → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110988309908640143483733510004 : ((((p5 ∧ ((p3 → ((((((p4 ∧ p2) → ((p4 ∨ p5) ∧ p2)) ∨ p2) ∧ p3) ∧ p1) → p5)) ∨ p5)) → (p4 ∧ p2)) ∧ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158277360605179186313550813055 : (((p1 → (p5 ∨ p2)) ∨ ((p4 → False) → (((False ∧ p2) → (False ∨ (False ∨ p3))) → (p5 → p1)))) ∨ (((p4 ∧ p4) → (p5 → p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322542218145266525930167022253 : (p5 ∨ ((p5 ∧ (True → (((p1 ∧ (p1 ∧ ((((True ∧ p4) → p5) ∨ (p5 ∧ (p3 ∧ p4))) ∨ ((p3 ∨ False) → p5)))) ∨ p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118811633588810640949552946598 : ((True → ((((True ∧ ((p2 ∨ p4) → p5)) → ((p1 ∨ True) → (p3 → (p3 → (p4 ∧ False))))) ∧ (p2 ∨ (p3 → False))) ∨ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319850199292861995715833068547 : (p4 ∨ ((((True ∨ p1) ∧ False) ∧ p1) ∨ ((((True → (p5 ∧ p3)) → p3) → ((p3 ∨ ((p4 ∨ (p3 → p4)) ∨ True)) ∧ p2)) → (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p5 ∧ p3)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609539212052312224859276601214 : (((((p3 ∧ (((p3 ∧ (p3 → (p1 → (p2 ∨ p4)))) ∨ (False ∧ ((p2 ∧ p2) ∧ ((p4 ∨ (p1 ∧ True)) ∧ p3)))) ∨ p5)) ∨ p2) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_41121420285179068107988914780 : ((((p2 → (p4 ∧ (((False ∧ p4) ∨ (False ∨ (p4 ∨ (p1 ∨ ((p5 ∧ False) ∨ p4))))) ∧ (p4 ∧ p2)))) ∧ ((p1 ∨ p1) ∧ p4)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212684293071607612840812213967 : ((False → ((p3 ∧ p3) ∨ True)) ∧ ((p4 → (((True ∨ p4) ∨ p5) → (p5 ∨ (((p2 ∨ ((p5 ∨ (False → p1)) ∨ p1)) ∧ p4) ∧ p4)))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647922804565562806698382006406 : ((((((p4 ∨ (True → ((p3 ∨ p2) → (((((p5 ∨ p3) ∨ p4) ∨ p1) ∧ (False → (p4 → False))) → True)))) → p3) ∧ p1) ∧ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204347648418074354931880378427 : (((False ∨ ((True ∧ p2) ∧ p3)) ∧ p1) ∨ ((p2 ∨ False) ∨ (True ∨ ((False ∧ (p5 ∨ p2)) ∨ (False ∧ (p5 → (False ∨ ((p2 → p2) → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351940564249050708830052107075 : (p4 → (((p5 ∨ (p4 ∨ p4)) ∧ (p2 ∧ ((p1 ∨ p4) → True))) → ((p4 → (p1 → (((p3 ∨ True) ∨ (p5 → p4)) ∧ (p5 ∨ p5)))) ∨ p2))) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h4.left
      let h11 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45611534049326689664068402645 : (((p3 ∨ (p5 ∧ (True → (((p4 ∧ p2) ∨ (((p1 ∨ ((p3 ∧ p2) ∧ p3)) ∨ (p5 ∧ False)) ∧ (p5 ∧ p2))) ∧ (True ∧ p1))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216677790487719314598058604316 : ((((p1 → p3) ∨ p4) ∧ p2) → ((((p5 → (True ∧ False)) ∧ p5) ∨ (p1 → (((True ∨ (False ∨ (p3 → p4))) ∧ p3) ∨ p1))) ∧ (True → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114924310889295054980192486028 : (((((False → (((False ∧ p4) ∨ False) ∨ (p2 → p2))) → p3) ∧ (p3 ∧ p2)) → (p4 ∨ (False ∧ (True ∧ (p5 ∨ (p4 ∧ p3)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139841576526487516976214220967 : (((p3 → ((((((False → (p3 → p3)) ∨ p5) → (p1 ∧ p1)) ∧ p1) → ((p3 → False) ∧ p1)) ∨ (True ∨ True))) → False) → (p1 ∧ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((((((False → (p3 → p3)) ∨ p5) → (p1 ∧ p1)) ∧ p1) → ((p3 → False) ∧ p1)) ∨ (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → ((((((False → (p3 → p3)) ∨ p5) → (p1 ∧ p1)) ∧ p1) → ((p3 → False) ∧ p1)) ∨ (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149358071108288546412760776638 : (((p5 ∨ p2) → ((p5 ∧ ((False ∨ False) → (False ∧ False))) ∧ (((((p5 ∨ p3) ∨ False) ∧ p3) ∧ p3) ∨ p2))) ∨ ((p2 ∧ p4) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167807737587356125474569328898 : (((((p3 ∨ ((p2 ∨ False) ∨ p5)) ∨ p5) ∧ (p3 → True)) ∧ ((p5 ∧ (True ∧ True)) ∨ p4)) → (((p3 → ((False ∨ p4) ∧ p5)) ∨ p2) ∨ True)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
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
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257688503507496833952183424228 : ((p3 ∨ p3) → (((((True ∨ ((p3 ∨ (((True → (p1 ∧ p4)) ∨ p4) ∨ False)) ∧ p1)) ∨ p5) → True) → p4) ∨ (p3 ∨ ((p3 ∧ p1) → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48344493852694265859125118941 : (((p3 ∨ (((p1 ∧ p3) ∨ ((p5 ∧ (p5 ∨ (((p3 ∨ (p5 ∧ p2)) → (p2 → (p3 ∨ p3))) → True))) → p3)) ∨ p4)) → (p3 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174320606007432451669120355521 : (((p1 ∧ (p2 → (p4 ∨ (p1 → ((p1 → p4) ∧ p2))))) ∨ ((p5 → p2) ∨ p5)) → (((False ∧ (p3 ∧ p3)) ∧ True) ∨ ((False → False) ∨ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42383702762324180614566821059 : (((p4 ∧ ((((((p3 ∧ p5) ∧ p3) ∨ p5) → ((p2 ∧ (True ∨ p2)) ∧ p5)) ∨ (p1 ∧ p5)) ∧ ((p1 → (False ∨ p1)) ∨ p4))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345592652285001036630048782462 : (p3 → (((p5 ∨ p2) ∧ (p4 ∧ ((p4 → p1) ∧ ((p3 ∨ (((False ∨ True) ∧ (p1 ∧ p4)) ∨ (True ∨ p3))) → ((False → p1) → p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657893811362020929549827211798 : ((((p1 ∧ (((p2 ∨ ((p5 ∨ p2) → True)) → (False ∨ (((False → (p3 ∧ False)) → ((True ∨ True) → False)) ∧ p5))) ∨ p5)) ∨ (True → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251841686698919813773624480224 : ((p3 → p5) ∨ (((p3 ∧ ((p3 ∧ False) ∧ (((True ∧ p5) → (p4 ∧ False)) → p2))) ∧ (p1 ∧ (True → (((p4 ∨ False) ∧ p3) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41363963244434378371669348030 : (((((p5 ∧ (((p5 ∧ ((False → (p3 ∨ p3)) ∧ p4)) → p1) ∧ p4)) → (p1 ∧ p1)) → (((p1 ∨ False) ∧ (p2 ∨ True)) ∧ p4)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158450129294873955333002989088 : (((p5 ∨ False) ∨ (p5 ∨ ((True → (((p1 ∧ p1) ∨ (False → p2)) → p3)) ∧ ((p3 → p2) ∨ True)))) ∨ (True ∧ ((p3 ∨ True) ∨ (False ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39288619675157028635631437699 : (((p1 ∧ (((((p5 → (p3 → p1)) ∨ p3) → (True → ((p4 ∧ p1) ∧ (p3 ∨ (p1 ∨ True))))) ∨ p4) ∨ ((p3 → False) ∨ False))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248825320236381736605506254204 : ((p3 ∨ p4) ∨ ((((True ∨ ((p2 ∨ False) → p3)) → p1) ∨ (p3 ∨ ((p1 → p5) ∨ True))) ∨ ((((False ∨ p2) → False) → True) → (p5 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_224233732044432700875222560854 : ((True → (False → p5)) ∧ (((p4 ∨ False) → p4) → ((p5 → (((p5 ∨ p4) ∧ True) ∧ (p1 ∧ p2))) ∨ (p4 ∨ (False ∨ ((p1 ∧ p3) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135800218878311099049044350703 : (((p2 ∧ ((p3 → (p5 ∨ False)) ∨ (((False ∧ p2) → (p2 ∧ p4)) ∨ p1))) → (((p4 ∧ False) ∨ (p2 ∨ True)) ∧ False)) ∨ ((p2 ∧ p4) → p4)) := by
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
theorem thm_5_vars_204694591300572499951207538763 : (((p3 ∨ ((p2 ∧ p5) ∨ p4)) ∨ p3) ∨ (False → (((((False → p2) ∧ (True ∧ p5)) ∨ p2) ∨ ((p2 ∨ p5) ∨ p1)) ∨ (p5 → (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318937177637191205848182774549 : (p4 ∨ ((((((True → p1) ∨ ((p5 ∨ (False → p3)) ∧ p5)) ∨ (p2 ∨ True)) ∧ p2) ∧ ((True ∨ p3) → (p4 ∧ p5))) → ((True ∧ p4) → p5))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h25 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h26 := h6 h25
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158944524217449906689891626139 : ((p2 ∨ ((((p1 → ((True ∨ p1) ∧ p5)) ∨ (p5 ∨ p5)) → p1) → (p5 → (p3 ∨ (p3 → p4))))) ∨ (((p1 ∧ p4) ∨ (True ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57718471682944464803621879770 : ((((True ∨ p1) → False) → (((p3 ∧ ((True → p4) ∨ ((False ∨ p1) → (p3 ∧ p5)))) ∧ p4) ∨ (p2 ∧ ((p3 → (p2 → p5)) ∨ p3)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190526516469577960405746308268 : (((((p1 → True) → (p2 → (p2 ∧ p4))) → False) → p3) ∨ (p3 ∨ (((((((p1 ∧ p4) → p4) ∨ p4) ∨ p2) → p4) → p2) → (False ∨ True)))) := by
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
theorem thm_5_vars_41287046635600592557650988194 : ((((((((p1 ∨ p5) ∨ p2) → (False ∧ p1)) ∧ (p1 ∨ p1)) → (((p1 → True) ∨ True) → True)) → (((p4 ∧ True) ∧ p5) ∧ True)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57981952127904015078000045729 : (((p4 → (True ∨ False)) → ((p1 ∨ p2) → ((((p4 → ((p1 ∧ p2) ∨ p3)) ∧ (p1 ∨ p4)) ∨ p1) ∨ (p5 ∨ ((p4 ∨ True) ∨ p5))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
theorem thm_5_vars_206476419971477637941470705956 : ((p5 ∨ (((False ∨ False) ∨ p2) ∧ False)) ∨ (p5 → (((True → (((True → p3) → False) → (p5 ∧ p2))) → (p1 ∧ ((p3 → p5) ∨ p1))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50119136286446453253507247824 : (((p1 ∨ (p2 ∨ (False ∧ (p1 ∧ (((p4 ∧ ((False → p2) ∨ p5)) ∧ (p3 → p1)) ∧ (p2 → True)))))) ∧ (False ∧ (True ∨ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52624229778445093256699354464 : (((((p5 → True) ∨ p2) → ((p1 ∨ p3) ∧ (p1 ∧ ((p2 → p4) → p4)))) ∨ (p5 → (p4 ∨ ((True ∧ (p5 ∨ p5)) ∨ (p5 → False))))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118892506176947103270009434740 : ((True → (p5 ∧ (p3 → ((p1 → p3) → (((p1 ∨ p1) → (True ∨ p3)) ∧ (((p2 → True) ∨ ((p3 ∧ False) ∧ p5)) → p1)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135494285168074019742436857570 : (((True ∧ (((p3 → True) → (p5 ∨ p2)) ∨ ((p4 ∨ ((p5 ∨ True) ∨ (p2 ∧ False))) → p3))) → ((p1 ∧ p5) ∧ p5)) ∨ (p3 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233680163902931595487403635301 : ((p2 ∨ (False → p5)) → (((p4 ∨ ((p5 → ((p3 → ((False ∧ (p5 → (p1 ∨ (p3 → True)))) ∧ p1)) → p3)) ∨ False)) ∨ (False → p1)) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656425626077600058660175619298 : (((((p3 ∨ (((p1 ∨ (p1 ∨ False)) ∨ (p4 ∨ True)) ∧ p4)) ∧ (p1 ∨ ((p3 → p4) ∧ (False ∧ (True ∧ (p5 ∨ p2)))))) ∨ (True ∨ p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_730109977429215926186096198221 : (((((p3 ∨ p5) → True) → (p1 ∧ ((p1 ∨ True) ∨ (p1 ∧ ((p5 ∧ ((True → ((p1 ∨ p1) ∨ True)) ∨ ((False → p2) ∨ p2))) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157149307861098203635197389701 : (((((((p2 ∧ p5) ∧ p4) ∨ ((((p2 ∧ p2) → p5) ∨ p3) ∨ p5)) → (False ∨ p5)) ∨ p3) → p1) ∨ (p5 → (p2 → ((p3 ∨ p3) → True)))) := by
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
theorem thm_5_vars_169565668566663129396633081426 : (((p4 → (((p1 ∧ p2) ∨ p4) ∧ (((True ∨ p3) → (p2 ∧ p4)) ∨ p4))) ∨ p1) ∧ ((((p3 ∧ p2) ∨ p5) ∧ p3) ∨ (False → (p5 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228180903720200282628760010639 : ((p5 ∧ (p2 ∧ p5)) ∨ (((p4 → ((((p1 → (p5 ∨ ((True → True) ∧ p2))) ∨ ((p5 ∧ p3) ∨ p4)) ∨ p1) ∨ p3)) ∨ p2) ∨ (p3 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299144233898907611684838314534 : (False ∨ ((((False ∧ (False ∧ p1)) ∧ ((False ∧ False) ∧ ((False → (p5 ∨ p5)) ∨ (p1 ∧ (p2 ∨ (((True ∨ p2) → False) → p3)))))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157046466849289098573526611712 : (((p1 ∧ ((True ∧ ((((p5 ∨ ((p4 ∨ p3) → p2)) → p1) ∧ (False ∧ False)) ∨ False)) ∧ False)) ∨ p5) ∨ (True ∧ (p2 ∨ ((True → p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342497204415485922195687484775 : (p2 → ((p3 ∨ (p4 → ((True ∨ (p5 → True)) → (p3 ∨ ((p1 ∧ False) ∧ True))))) ∨ (p3 → (((p4 ∧ p3) → p5) ∨ ((True → False) → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691442617972513410504163795265 : (((((p5 ∧ p4) ∨ ((p3 ∨ (p1 ∧ (((p4 ∨ p4) ∨ p4) ∨ p2))) ∨ (p2 → p3))) → ((((True → (False → p2)) ∨ p1) → p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157004158582130187411979513862 : (((((False ∧ p2) ∨ False) ∧ (((p2 ∨ (p1 → ((p1 → (p5 ∨ True)) ∨ p3))) ∧ p3) ∨ p5)) ∨ p3) ∨ (True ∨ (((True ∧ p2) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164804800894721236570871422446 : (((((p2 ∧ p3) ∨ p4) → ((((((False ∨ p5) → True) ∨ p4) → p1) ∧ p2) → False)) ∨ True) ∨ ((p4 ∧ ((False ∧ (p3 → p5)) ∧ p1)) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47075919817279696490946641962 : ((((((p2 ∨ ((p3 ∧ (p2 → False)) → p2)) ∨ (((((p4 ∨ p3) → p4) → p2) → p4) ∨ p1)) ∧ p5) → (p3 → p2)) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171772328675249150868216128196 : ((((p3 ∨ ((p5 ∧ ((p3 ∧ ((p3 ∧ p5) ∨ p2)) ∨ True)) ∨ True)) → False) → p4) ∨ ((p3 → ((p1 ∨ False) → p2)) → ((True ∧ p1) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p5 ∧ ((p3 ∧ ((p3 ∧ p5) ∨ p2)) ∨ True)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53696309865201520751773888307 : (((p5 ∧ ((p5 ∧ ((p1 → (p3 ∧ True)) → p4)) ∧ p4)) ∧ (((True ∨ p4) ∨ (p2 → p4)) ∧ (False ∨ (p1 ∧ (p5 ∨ (p5 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165115156806267246332090653344 : (((p3 → (p5 ∧ ((((False ∨ p3) ∨ (((p2 → p2) → p5) ∧ p4)) ∨ p3) → p2))) → p2) ∨ (((p4 → True) → p2) ∨ (False ∨ (True → True)))) := by
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
theorem thm_5_vars_38109936042795613946517923726 : ((((((p4 ∨ ((p3 → (p1 ∧ p4)) ∧ (p1 ∧ (p1 → False)))) ∧ (p5 ∧ (True → (p5 → p3)))) ∨ p1) ∧ (p5 ∧ (True ∧ False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216967077470295644077605707848 : (((p2 → (p1 → p5)) ∧ p5) → ((((p1 → (True ∧ True)) → (True → (p4 ∨ p4))) ∨ (p3 → True)) ∧ (((p3 → p1) ∧ p4) ∨ (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45634339490126148345483482191 : (((p4 ∨ (((((True ∧ (False ∧ p2)) ∨ True) ∨ ((p4 ∨ (p3 ∨ (p1 → p3))) ∨ (False ∨ p5))) ∨ p5) → (p1 → (p3 ∧ p3)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618874708034221074802464605850 : (((((p5 ∨ (p4 ∨ True)) ∧ ((((p5 ∨ (((((((True ∨ False) ∧ True) → p4) ∧ p4) ∧ p1) ∧ p2) → False)) → p5) ∧ p3) ∨ True)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_56063800841798526799046209928 : (((((p5 ∨ p1) → p4) → p2) ∨ ((((p4 ∧ True) ∧ (((p1 → True) ∧ p5) ∨ (((p5 ∧ p2) ∨ (p3 ∧ p3)) ∨ False))) ∧ p3) → p4)) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340801304481891891512256541631 : (p2 → (((p2 ∨ (p2 ∨ (p2 ∧ ((((True ∧ p2) ∧ (((p5 ∨ False) → (p3 → False)) → (p4 → False))) ∨ True) ∨ (p1 ∧ p5))))) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214791404063867817565977331308 : (((p1 ∨ p1) ∨ (p2 → False)) ∨ ((p2 ∧ False) ∨ ((((True → (p5 ∨ (p2 ∧ True))) → True) ∨ (((p3 → p2) → (True ∨ p4)) ∧ False)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110762576785812101013053460163 : ((((p2 ∨ (p3 → ((((p4 ∧ p1) → (p4 ∧ True)) → ((p1 ∨ p4) ∧ (p2 ∧ True))) ∨ (p1 ∧ (p2 → p1))))) ∧ False) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347143048633596327107847425871 : (p3 → (((False → p5) ∧ (((((p1 → False) ∨ False) ∧ (False → p3)) → True) ∧ p2)) → (p5 → ((p3 → (p5 ∨ (p1 ∨ (True → True)))) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700674872142711636936001139323 : ((((p4 → (False ∨ (p3 ∨ (p5 ∨ ((True → (False → p4)) ∨ p1))))) → (((((p3 ∧ p1) ∨ (True ∧ p1)) → True) ∧ (p3 ∨ p2)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330540270957851493031208715965 : (True → (p5 ∨ (((True ∧ (False ∨ ((p1 ∨ p4) ∨ False))) → (p3 ∨ ((p2 ∧ (p2 ∧ p5)) ∨ (True → (False ∨ (False ∧ (p1 ∨ p3))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192032813004436045658981662564 : ((p2 → (((p3 ∧ p4) ∧ p4) ∧ ((False ∨ True) ∨ p5))) ∨ (p5 → (((p5 ∧ ((p4 ∨ p5) → p5)) ∨ p1) → (p3 → ((False ∨ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166414740170628484809535139550 : ((p1 ∨ ((True ∨ (p5 → ((p5 ∨ (((p2 ∧ p1) ∧ p2) ∨ (False → p5))) ∧ p5))) → False)) ∨ (p4 → (p3 ∨ ((p5 → p3) → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39022950509960415365951018239 : ((((p1 → False) ∧ (((False ∧ (((p4 ∧ True) → False) ∧ (p4 ∨ (((p4 → p1) ∨ p3) → (p1 ∨ False))))) ∧ (p3 ∧ False)) ∧ p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700642982603178261458753436033 : ((((p3 → ((False ∨ (False ∨ (p5 ∧ ((p3 → True) ∧ p4)))) → p1)) → (((p5 ∨ (p3 → (((p3 → p3) ∧ p5) ∨ p3))) ∨ p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229582127349145708278843669156 : ((p3 → (False ∧ True)) ∨ ((p2 → (p2 ∨ p4)) → (((((False → p1) ∧ (p3 → (p2 ∨ False))) ∨ (False ∨ p2)) ∨ ((True ∨ p2) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509599558256284830239338877 : (((((p4 ∧ True) → (p3 ∨ (((p5 ∨ (False ∧ p1)) ∧ (p4 → ((False ∧ p4) → (True → False)))) → p3))) ∨ True) → p4) ∨ (True ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114162626556287054305743710851 : (((((((p2 ∨ (False → (True ∨ p2))) ∨ p1) ∧ True) → (((p5 → (False → p5)) ∨ p3) → p2)) → p3) → ((p4 ∧ p4) → p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194147301972830278979372678100 : ((p1 → ((p4 ∧ p2) ∨ ((p4 ∨ p1) ∧ (p3 ∨ p3)))) → (((p1 → p2) ∨ True) ∧ (True ∨ (((p3 → True) ∧ ((p4 ∧ True) ∧ p2)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_690661546279556366794673607787 : ((((((p4 ∨ p2) → ((p2 ∨ (p2 → (p3 → (True ∨ p1)))) ∧ (False ∨ p5))) ∨ p2) → (p5 ∨ (((True → True) ∧ (p4 ∧ p4)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200314398315407005865550614595 : (((p4 ∧ p3) ∧ (p5 ∧ (p4 ∨ (p5 ∧ p5)))) → ((((True ∧ p1) → p4) → (((True → p1) ∧ ((p5 ∧ True) → False)) ∧ p1)) ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167897765313266404717453662375 : ((((((p2 ∨ False) → p3) → (p1 ∧ p3)) → p2) ∧ ((p1 ∧ True) → (False ∧ (p5 → p5)))) → (p1 → ((p4 ∨ ((False ∧ False) ∨ p3)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43036682767144341807643078184 : ((((((p3 → (True ∨ (p3 ∨ (p5 ∨ (p5 ∧ p3))))) → (((False ∨ (False ∨ p3)) ∨ (p4 ∨ (False → p1))) → p4)) ∨ True) ∧ p3) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153609038599533915244903478597 : ((False → (p3 → (((False → ((((p4 ∨ (p3 → p2)) ∧ p4) ∧ p5) ∧ False)) ∨ True) → ((False → p2) ∨ p5)))) → (((False → p4) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322431586927953067089765944302 : (p5 ∨ (((((p1 ∨ (p1 ∨ p3)) ∨ p3) ∨ p4) ∨ ((p2 ∧ p1) → (((p4 → True) ∧ (True ∨ (p1 ∧ True))) ∨ ((p1 ∨ p2) → p4)))) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323687690368197042124978461168 : (p5 ∨ ((p5 ∨ (((p1 ∨ (p5 → (((p1 ∧ (p5 ∨ p2)) ∨ (True ∧ p5)) ∨ (p5 ∨ p1)))) ∧ True) → p5)) ∨ (p3 ∨ ((p1 ∧ True) → True)))) := by
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
theorem thm_5_vars_313486989090748276986208038420 : (p3 ∨ (((False ∨ ((True ∧ True) → ((((p5 → (p2 ∨ p1)) → (p1 ∨ (False ∧ ((p1 → (p3 → p3)) → p2)))) → p5) ∨ True))) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((True ∧ True) → ((((p5 → (p2 ∨ p1)) → (p1 ∨ (False ∧ ((p1 → (p3 → p3)) → p2)))) → p5) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242122508977025188945484984814 : ((p2 → True) ∧ ((((((p4 ∧ (False ∧ p2)) ∨ ((((p5 → True) → p1) → True) ∧ p4)) ∧ p2) ∧ ((p3 ∨ p4) ∧ (p5 → p5))) ∧ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191244720252933245157074217115 : (((False ∧ p2) ∧ (p2 → (p1 ∧ ((p1 → True) ∧ p4)))) ∨ (True → ((True → ((True ∨ p2) → (((False ∨ p5) ∧ (p1 ∧ False)) ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161593652614190242277152618248 : ((True ∨ (False ∨ (p5 ∧ (p5 ∧ ((p3 ∧ (False → p3)) ∨ ((((p4 → p3) → p2) → True) ∨ p1)))))) → ((((p1 ∧ p2) ∧ p5) ∧ p5) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786022050775443748795806970406 : (((p4 ∨ ((((((p1 → p1) ∧ ((((False ∧ (p3 ∨ (True → p3))) ∧ (True → p1)) ∨ p5) ∧ True)) ∧ p4) → p2) ∨ True) → (p2 ∨ True))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585918410728740275624149500446 : ((((((False ∨ (p4 → (p5 ∨ ((p1 ∨ ((False → True) ∨ ((p1 ∧ True) → True))) ∧ (p4 ∨ (p2 → p5)))))) ∨ (p2 ∨ p3)) ∧ p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66732083088087862018552802481 : ((True → ((False ∨ p4) → (((p1 → (((p2 → p3) ∨ p5) ∧ False)) ∧ ((p4 → ((((p1 ∧ False) ∧ p4) ∨ p3) ∨ p5)) ∧ p2)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149499369194556998666653710367 : ((p1 ∧ ((p4 ∨ (p3 ∨ (False ∧ ((p2 ∨ True) ∧ (((p2 ∨ p4) ∧ (p2 → p4)) → p5))))) ∧ (p1 ∨ p2))) ∨ (p2 → ((False → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187045719175424683093771340932 : (((p3 ∧ True) ∧ ((p5 ∨ (p2 → (p4 → p4))) ∧ (True ∨ p4))) → ((((p2 → p4) ∨ p2) ∨ False) ∨ (p2 → ((False → False) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773613416109976408800615360250 : (((False ∨ ((p1 ∧ (False ∧ ((((p1 → p3) ∨ False) ∧ (True ∨ p1)) ∨ (((p1 → p1) ∨ p5) → (p2 → ((p4 ∨ False) → p4)))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41089005911618855301981295413 : ((((((((False → ((p4 → (False → p4)) ∧ p4)) ∨ False) ∧ (False ∨ ((p2 → p1) ∨ p5))) → p3) → p3) ∧ (p2 ∧ (p2 ∨ p5))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227832520964463700490133006168 : ((p2 ∧ (p3 ∧ p5)) ∨ ((True → (p1 ∧ True)) ∨ ((p5 ∨ p5) → (((((p2 ∧ False) ∧ p1) ∧ p5) → p5) ∧ ((p4 ∧ (p4 ∧ p5)) ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8
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
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52615028243405466762301506023 : (((((p3 ∨ False) ∧ True) ∧ ((p5 ∨ ((True → False) ∨ (p5 → p5))) ∨ p5)) ∨ (p4 ∧ (p2 → ((p4 ∨ (p5 → (p2 ∨ p5))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134624645062678978725135737609 : ((((p3 ∨ ((p3 ∨ p1) ∨ (True ∨ ((p3 ∧ (p4 ∧ p2)) → (p4 ∨ (p5 → p3)))))) → (True → (p4 → p2))) → p3) ∨ ((p5 ∨ True) ∧ True)) := by
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
theorem thm_5_vars_171983709806040876895723443611 : (((p4 → ((p3 ∨ ((p4 ∨ p3) → (p4 → (p2 ∧ p3)))) ∨ True)) ∧ (p4 → p5)) ∨ (p4 → ((p2 → (True ∧ True)) → ((False ∨ p5) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



