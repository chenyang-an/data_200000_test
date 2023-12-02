variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703845125595435196263350039349 : ((((((p3 ∨ (((p2 ∨ p1) → p3) ∨ p1)) → p3) ∨ p3) → (((((True ∧ (True → p3)) ∧ p1) → p1) ∧ p1) → (p3 ∧ (False ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114138339563715756106872167737 : (((((((p3 ∨ True) → p2) → False) ∧ ((((p3 ∨ p4) ∧ (p4 ∨ p2)) ∧ (True → p5)) ∨ p3)) ∧ p1) → (p2 → (p4 ∧ p1))) ∨ (p2 → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : ((p3 ∨ True) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h14
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h19 := h5 h15
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h23 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h24 : ((p3 ∨ True) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h28 := h5 h24
    -- False on the left can always be used.
    apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h40 =>
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h42 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h43 =>
        -- One of the premise coincides with the conclusion.
        exact h30
  case inr h44 =>
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214425370531547295408715642473 : (((p3 → (p3 ∧ True)) → False) ∨ (((True ∧ (((p3 → (p2 ∧ False)) → ((False ∧ p1) ∧ p3)) ∨ (False → (p2 ∨ (p5 → p4))))) ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60010188693451666294937529231 : (((p1 ∨ True) → (((p4 → p2) ∨ ((((p3 → (p5 ∨ False)) → p5) → (p1 → p5)) → p4)) ∨ (((p2 → p5) ∨ False) ∨ (p5 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165322998105295964821365388519 : (((((p3 ∧ (p4 → (((p5 → p4) ∧ p5) ∨ False))) ∧ p3) ∧ p3) ∧ ((True ∨ p4) ∨ p4)) ∨ ((((p5 ∧ False) → False) → (p5 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198933513162070132593927600554 : ((p4 → ((p2 → (p5 ∧ (p5 ∨ p5))) ∨ p3)) ∨ ((p5 ∧ ((p3 ∨ False) → p1)) → ((((p1 ∧ True) ∨ (p4 ∨ p1)) → p5) ∨ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663467554284635326740510985667 : (((((True → p3) → ((((True ∨ False) → p3) ∨ (p1 → ((p1 → ((p4 ∨ p1) → (False → p2))) ∧ (p4 ∨ p1)))) ∧ p5)) → (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227808631396929739006728190124 : ((p2 ∧ (True ∧ p3)) ∨ (p4 ∨ ((((False ∧ (((p4 ∨ True) ∧ (False ∧ p1)) → (((p5 → p1) → True) → p2))) → p3) ∧ p3) ∨ (p2 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221766050231199244410363456344 : (((p1 ∧ p3) → True) ∧ ((True → p3) → (p3 ∨ ((p4 ∨ p2) ∨ ((((p2 ∨ (p4 ∧ (p3 ∨ p1))) ∧ (True → p3)) ∨ (p4 → True)) ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810974277343029320542721224966 : (((p5 → ((p2 → p1) → ((True → (((p2 → (True ∨ p1)) → p1) ∨ p3)) ∨ ((((p4 ∧ ((p5 ∧ p3) ∧ p2)) ∧ p4) → p4) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265741333466200495999793899471 : (True ∧ (p3 ∨ (p4 ∨ (((False → (p1 → p5)) ∨ p5) ∧ ((p3 ∧ False) ∨ (p1 ∨ (False → ((True ∧ (True → ((p3 ∨ p4) ∧ p3))) → p3)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217747512127705257385285033912 : (((p3 ∧ (p5 ∨ True)) → False) → ((((((p3 ∧ False) ∧ (p3 ∧ p4)) ∨ p2) → (((False ∨ p3) ∧ True) → p1)) → p3) ∨ ((p3 → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692248854753277331147589427784 : (((((p4 ∧ ((p3 ∧ (((True ∧ (p1 ∨ p5)) ∨ True) ∧ p2)) ∨ True)) ∨ p3) ∧ ((True ∧ (False ∧ p4)) ∧ (p5 ∨ (p5 → (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682207002021768393839717878403 : (((((p1 ∧ (((((p2 ∧ p1) ∧ p2) ∨ (p1 ∧ p1)) ∧ (p2 → p3)) ∧ (p4 ∨ p4))) → p3) ∧ ((p3 ∨ p2) ∨ (False ∧ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780494168996212986992461717779 : (((p2 ∨ ((((p3 → p3) ∨ ((True ∨ p1) ∧ p2)) ∨ (p4 ∨ (p2 → (False → p4)))) → ((p4 ∧ True) ∨ ((p3 ∨ (p1 → p1)) ∨ p1)))) ∨ p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652828972827983624523975428052 : ((((p3 ∨ ((p5 ∨ (((p3 → p1) → (p2 ∧ (False ∧ p2))) → True)) → ((p1 ∨ True) ∨ ((p2 → p1) → (p1 ∧ p1))))) ∧ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593142842140610398289917949489 : (((((((False ∨ ((True → p2) ∨ p2)) ∨ ((p1 ∧ p5) ∧ True)) → ((p5 → ((p2 ∨ p1) → True)) ∧ p1)) ∨ (False → (p1 → False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64050827417589955423785842538 : ((False ∨ ((((p4 → ((False ∧ ((p4 ∨ (True ∧ p3)) ∧ (p3 ∨ p3))) ∧ True)) ∧ (p5 ∧ p3)) ∧ p4) ∧ ((False ∨ p1) → (p5 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172926725520959464146736625079 : ((p3 ∧ ((p2 ∧ ((False ∨ (p3 ∨ p2)) ∧ (p3 ∧ ((False ∨ p1) ∨ False)))) ∧ p5)) ∨ (p3 ∨ ((True ∧ ((p2 → p1) → (True ∨ p3))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41113784811223132932144010505 : ((((p3 ∧ (True → (p2 ∧ ((((((True ∧ True) ∨ (p5 ∧ p1)) ∧ (p1 ∨ True)) → p3) ∨ p2) ∧ p3)))) ∧ ((False ∨ p4) → p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611511590791856500414214997920 : (((((p4 ∧ (p1 ∨ (((p1 → ((p3 ∧ (p5 ∧ p4)) ∨ p5)) ∨ ((p5 → (((False → p5) ∧ p1) → p2)) ∨ p1)) → False))) → p5) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110803591074328773297681867023 : ((((((((p1 ∨ ((p1 ∧ (p5 ∧ False)) → True)) → (p1 ∨ p2)) ∨ (p4 ∧ p1)) ∨ p5) → ((p5 ∧ p4) → p1)) ∨ p3) ∧ p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135366824425354475137043024174 : (((((((((p1 ∧ p2) ∧ True) ∨ (p4 → (True ∧ False))) ∨ True) → (True ∧ p4)) ∨ p4) ∧ p5) ∨ (p2 ∨ (False ∨ p4))) ∨ ((p1 ∧ p5) → p1)) := by
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
theorem thm_5_vars_157037585969951150655317948195 : ((((p1 → p5) → (p5 ∨ ((p3 ∨ p4) ∧ ((p2 ∧ (p3 → p3)) ∨ ((False ∨ p3) ∨ False))))) ∨ p2) ∨ ((p1 ∨ p1) → (p3 ∨ (True ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_895800538000687889044306925058 : (((((p1 → ((((p5 ∧ p2) → (p1 → ((True ∧ False) ∨ (p4 ∧ True)))) → p2) ∨ (p2 → (True ∨ False)))) → False) ∨ ((p5 ∨ p5) ∧ p3)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 → ((((p5 ∧ p2) → (p1 → ((True ∧ False) ∨ (p4 ∧ True)))) → p2) ∨ (p2 → (True ∨ False)))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h3
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137673206823548871236107758967 : ((False ∨ (p2 → (p1 ∨ ((((p4 ∧ True) → (p1 ∨ p3)) ∨ ((p3 ∨ p3) ∨ (((p3 ∨ p4) ∧ p4) ∧ p5))) ∧ True)))) ∨ (False → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199855937460909450545739801157 : (((False ∨ (p3 ∧ (True ∨ p1))) ∧ (p5 ∧ p4)) → (p5 → (((p5 → (((p3 → ((True ∨ (p4 ∨ p4)) ∨ False)) ∧ p2) ∨ True)) → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h4.left
      let h11 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251564699199876234837648425106 : ((p3 → False) ∨ (((True → False) → (p4 ∧ True)) ∧ (((((False → (p5 ∨ p2)) ∨ p1) → ((p3 ∧ True) ∨ (p5 ∧ False))) → p5) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653721628478657747601149128306 : ((((((((True ∨ True) → (p5 ∧ (p4 ∧ (True ∧ False)))) ∨ ((((p3 → p2) ∨ False) → p1) → p2)) ∧ (p3 ∨ p1)) ∧ p1) ∨ (p2 → p2)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_98917380767871452701859412127 : ((True → (((p5 ∧ (p1 ∧ (True → p4))) → ((True → (True → (p5 → p4))) → ((((p1 ∧ False) → p3) → p4) ∨ p1))) ∧ (p5 ∧ False))) → p1) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48972940616972791124690668881 : (((((False ∨ (p4 → ((True → (p3 ∨ ((p5 ∧ ((True → p5) ∧ p5)) ∨ p5))) ∨ p4))) ∧ (p3 ∨ p4)) ∨ True) ∨ ((False ∧ p2) ∧ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135993790465964333389036609403 : ((((p1 → p4) ∧ (((p5 ∧ p2) ∨ (True ∧ p5)) ∨ False)) ∨ (((p4 → False) ∧ ((p4 ∧ p1) ∨ (p2 → True))) ∨ True)) ∨ (p4 → (True ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111711882187156530469194141738 : (((((((p1 ∨ (p2 ∧ (p3 → (p3 ∧ False)))) ∨ (p5 ∨ p4)) ∨ p4) ∨ ((p2 ∨ ((p5 ∧ False) ∧ False)) ∨ p4)) → p3) ∨ True) ∨ (p2 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351402309158533426155585363609 : (p4 → (((((p4 → p2) → ((False ∧ ((p1 → (p1 → p2)) → p5)) ∧ True)) ∨ p1) ∨ ((p3 ∧ p3) ∨ p3)) ∨ ((p4 ∧ (p2 → True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68087525388438245324068050738 : ((p2 → (p5 ∨ ((((((p5 ∧ p2) ∧ (True → (p1 ∧ (p2 → True)))) → (((True ∧ p2) ∨ p1) → (True ∧ False))) ∨ p2) ∨ p1) ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322486466334170461067763670463 : (p5 ∨ (((p1 ∨ p4) ∨ ((((True ∧ (p3 ∧ True)) ∨ p2) → (p5 → p1)) ∧ (((p4 ∨ ((p3 ∧ True) → p1)) ∨ (p3 ∨ False)) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188291425591481041004255684479 : (((p5 ∨ (p1 ∧ ((True ∧ False) → (p1 → False)))) ∨ True) ∧ (((p4 ∨ (p2 ∨ False)) ∨ True) ∨ (True ∧ (((False ∨ p2) ∨ True) ∧ (False ∨ False))))) := by
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
theorem thm_5_vars_51981035127159391140173915917 : ((((p3 → False) ∧ ((False ∧ ((p1 ∨ (p3 → (p3 ∧ p4))) ∧ (p2 → p1))) ∧ p1)) ∨ (False → (((p4 ∧ p1) → (p2 ∨ p5)) → False))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213828576239481622445018576780 : (((p5 ∧ (True ∧ p5)) ∨ False) ∨ ((p1 ∨ p3) ∨ (((p3 ∨ (p5 ∨ p1)) → ((p3 ∨ ((True ∨ False) ∧ True)) ∧ (p4 → (False ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62578227210211807979231433058 : ((p3 ∧ (p1 → (((p4 ∧ (p4 ∧ ((p5 → p4) → p4))) → ((p3 → (p2 ∨ p4)) ∧ (((p1 ∨ p5) ∨ (False → p5)) → False))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180260022015277677239932946023 : (((p4 ∨ (((p1 → ((False ∨ (p1 ∧ p1)) → p4)) ∧ p3) ∨ True)) → p4) → ((p3 → ((p2 → ((False ∧ (p5 ∧ p4)) ∨ p1)) ∧ p5)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ (((p1 → ((False ∨ (p1 ∧ p1)) → p4)) ∧ p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114613481129356397713134085224 : (((p1 → (((p2 ∨ False) → ((((p2 ∧ False) → p1) ∧ p3) ∧ (p3 → p3))) → p2)) ∧ ((p5 → ((p3 → p1) ∧ p3)) ∧ True)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262487812147507743526801385363 : (True ∧ ((True → (p2 → ((True → ((False → True) → ((p4 ∧ True) ∨ (((False ∨ (p3 ∨ ((p3 ∧ p5) ∨ p3))) ∧ p4) ∨ p4)))) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324736678418497107067789358668 : (p5 ∨ ((p2 ∧ (p3 ∧ True)) → (False ∨ (((p1 → (((p3 → True) ∧ False) ∨ True)) ∧ (p5 ∧ (p5 ∧ ((p3 ∧ (p4 ∧ p1)) → p1)))) ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179191165273014495572521328698 : ((p3 ∧ (((p2 ∧ True) ∧ p2) ∨ ((True ∨ p4) → (p3 → (p2 → p4))))) ∨ (((p5 ∧ True) ∨ (False → (((True ∨ p1) → True) ∧ True))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253968569911515870845779297626 : ((p1 ∧ p5) → (((p4 ∨ p1) → (True → (((p5 → (((((False ∧ (p2 ∧ p5)) → p1) ∨ p3) ∧ p4) ∨ p5)) ∧ (p5 → p5)) → p3))) ∨ p1)) := by
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
theorem thm_5_vars_49243730847271649657797156089 : ((((p5 ∨ p5) → ((True → (((p4 ∧ True) ∨ p1) ∨ ((p1 ∨ p2) ∨ (p2 → (p4 → (p3 ∧ p5)))))) ∨ p4)) ∨ ((False ∧ p4) → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_178875441904347938491321051246 : (((p1 ∧ False) ∧ ((((p3 ∨ (p3 → p3)) ∧ p1) ∨ (p2 ∨ p1)) ∧ p2)) ∨ ((p5 ∧ p4) ∨ ((False → p2) ∨ ((p5 → (p3 → p3)) ∨ p4)))) := by
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
theorem thm_5_vars_197870634189701464908565890318 : ((((p3 → p2) ∧ p2) → ((p5 ∨ p1) ∧ p2)) ∨ ((True ∨ (((True ∧ True) ∧ p1) → p1)) → (((p3 ∧ (True → p5)) → p5) ∨ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54689081700008180266079407582 : ((((p1 ∨ ((p3 ∨ p5) → (p4 → True))) → p4) → (((((((True → p5) → p2) ∧ (p5 ∧ p4)) → True) ∧ (False → p5)) → p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44292258580482617527078565204 : ((((((p4 ∧ ((p1 ∧ p1) → True)) ∨ True) ∨ (p4 ∧ (False ∨ ((p2 ∧ p2) → True)))) ∧ (p1 → (True ∨ ((p3 ∧ False) ∧ p4)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392079356139956388778937893075 : (((((p2 → ((p5 ∨ p3) → p1)) → ((p2 ∨ p4) ∨ (p3 → ((((p5 ∧ p3) ∨ p5) ∧ (p4 → ((p3 → True) → p5))) ∧ p2)))) ∨ True) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330620626260963986253063848713 : (True → (True → (((p3 → (p1 ∧ (True → (True → p2)))) → (((p1 ∧ p5) → False) ∧ p1)) ∨ ((p3 ∨ ((p2 ∧ (p1 → p2)) ∨ p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66436168035840330843522145172 : ((True → ((((p4 ∨ (((p4 ∧ (((((True ∧ p5) → ((True → p3) ∨ p2)) ∧ True) ∨ p2) → p5)) ∨ p3) ∨ p5)) → p5) ∨ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322291089940297839939781608048 : (p5 ∨ (((((((p5 ∨ ((True ∨ (False → False)) → (False ∧ p1))) → False) → (False ∧ p5)) → p3) ∧ (((p1 ∧ False) ∧ p1) ∨ p3)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254350353865846634561381160515 : ((p2 ∧ p4) → (((p4 → p2) ∧ ((((p5 → p5) ∨ ((p4 ∨ p1) ∨ p1)) → (p4 ∧ p5)) ∨ p4)) ∨ (p3 → (((p2 → p5) → False) ∧ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41846450519602406451805304161 : ((((False → (p2 ∨ False)) ∧ (False ∨ ((p1 → (((p2 ∨ (p4 ∨ p3)) ∧ (p5 ∨ p5)) ∨ ((p1 ∧ True) → p5))) → (p4 → p3)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43485851768222425626162597800 : ((((p2 ∧ (p2 → ((((p3 ∧ (p3 ∨ p3)) → (p5 ∨ False)) ∨ ((p2 → ((p4 ∧ (p2 ∨ p5)) ∧ p2)) ∨ p3)) ∨ p2))) ∨ False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326341390974166673916702530974 : (p5 ∨ (p5 → (((((p1 ∧ (((p5 → ((p3 ∨ p2) ∨ (p2 ∧ p1))) → False) → (p4 → p1))) → p2) → p2) → ((False ∧ p4) ∧ p5)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57108181672612643985030941483 : ((((p1 ∨ False) ∧ p1) ∨ (((p3 ∨ p1) → ((p2 ∨ p4) → p4)) ∧ ((((p2 ∨ p2) → (False → p3)) ∨ (p1 ∧ (True ∧ False))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52056825927732466614362152106 : (((p4 → (((((True ∨ p1) ∨ p3) ∧ ((p1 ∧ p1) ∧ p4)) ∧ p4) ∨ (True ∧ p1))) ∨ ((False ∧ ((True ∧ False) → (p2 ∨ p2))) → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_164862381537888077477850058803 : (((p2 ∨ (p2 ∧ (p4 ∨ (((((p1 ∧ (p4 → p1)) → p2) ∧ p3) ∨ True) ∨ p1)))) ∨ True) ∨ ((((p2 ∨ p2) ∨ (p3 ∧ True)) ∧ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620833189548972614633280593270 : (((((False ∨ p1) → (((((p1 ∨ (p2 → p1)) ∧ (p5 ∨ (False ∨ (p5 ∨ p3)))) ∨ p2) → ((False ∨ p3) ∧ (p4 ∧ False))) → p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184952735762649978597184913491 : ((((p5 ∨ p2) ∨ p5) → (p3 ∨ (p3 ∨ (True ∨ (p1 ∧ p3))))) ∨ ((p1 ∧ ((p4 ∧ p5) ∧ (p4 → (p2 ∧ p5)))) ∨ ((False ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_150328946400157066161918919942 : ((p5 → (((p1 ∨ p3) → (((((p4 → p5) → p1) ∧ p3) ∧ p4) ∧ ((p5 ∨ (False ∨ p5)) ∨ p5))) ∧ False)) ∨ (p3 → ((True ∧ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217890490169303389763192781299 : (((p2 → (p4 ∨ p2)) → False) → ((((p3 ∨ (p4 ∧ ((False ∨ (True → True)) → p2))) → True) ∧ p1) → ((p5 ∧ (p1 → p5)) ∨ (p5 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → (p4 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467893491295397674144803808314 : (((((p3 ∨ p3) ∨ ((((p5 ∧ p2) → p3) → p3) → ((True ∨ p3) → False))) ∨ (False → (p1 ∧ (p5 → ((p3 ∨ (p2 → True)) ∧ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213440144785681015425168991307 : (((p4 ∨ (p1 → p4)) ∧ p1) ∨ (p1 → (p4 → ((p3 ∨ (False ∨ (p3 → ((p3 ∨ p4) ∧ (((p4 → p3) ∧ p1) ∨ p3))))) ∨ (p5 ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689663552106974068424656829386 : ((((((p3 ∨ (p3 ∨ False)) ∨ False) ∨ ((p2 ∨ p5) ∨ (True ∧ (p1 ∨ (p2 ∧ p3))))) ∨ ((((p3 → p5) → p1) ∧ p1) → (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343229795527934966417601496968 : (p2 → ((p2 ∧ (p1 → p2)) → (((True → (p2 → (p5 ∨ (p4 ∨ (p2 ∧ p5))))) ∨ True) ∨ ((p2 ∨ (True ∧ (p2 ∨ p5))) ∨ (p4 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141311950883701151906099281317 : (((p2 → (True ∧ (p4 ∧ True))) ∧ (p5 → (p2 ∧ (((p2 ∧ p4) ∨ ((((p1 → p3) ∧ p1) ∨ p1) → p5)) ∧ p2)))) → (p2 → (p4 ∧ True))) := by
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
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43403014542957523951980493690 : (((((p5 → ((p4 → (p2 ∧ ((False ∨ (True ∨ p1)) → p5))) ∧ p1)) ∧ ((p1 → ((p3 → (p2 → True)) ∧ p1)) ∧ p5)) ∨ p1) → p1) ∨ False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323245654026687513026971466781 : (p5 ∨ (((True → p5) ∨ ((p2 → (((p1 → (p4 ∧ True)) ∧ p5) → ((True → ((False ∧ p5) ∨ p3)) ∨ False))) ∧ (p1 ∧ p4))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586026262568474938887772719477 : (((((((True → p5) ∨ (((((p2 ∨ p4) → p2) → False) ∨ ((p3 → p1) ∨ False)) ∧ (p3 ∧ p3))) ∨ ((True ∨ p2) → p5)) ∧ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110775173594708568608498921122 : (((((((True → (((p5 ∨ p1) ∧ p4) ∨ False)) ∨ ((False → p2) ∧ (False ∧ (p1 ∨ True)))) ∧ (p1 → True)) ∧ p4) ∨ True) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208911537462923943308792574876 : ((p5 ∧ ((p4 ∧ (False → p2)) → p4)) → (p2 → (((p2 ∧ ((((p1 → p4) ∨ (False ∧ (p2 → p4))) ∨ p2) → p2)) ∧ (p4 ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179176716697842079748427529563 : ((p3 ∧ ((((p1 ∨ p1) → p4) → (((p4 ∧ False) ∧ p3) ∧ p4)) ∧ p4)) ∨ (p1 ∨ (p4 → (False → (p4 ∧ (p4 ∨ ((True → p5) ∧ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754325819631990675557079924178 : (((False ∧ ((False ∨ p3) ∨ (((False → p3) → p5) ∧ (((False ∧ (False ∨ (p4 ∨ ((p2 ∨ (False ∧ p5)) → False)))) ∧ (p1 ∨ p4)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623054149880046459614977345660 : ((((p5 ∧ (p3 ∨ (p3 ∧ ((((True → p2) → True) ∧ (p5 ∧ ((((p5 ∨ (p5 ∧ p4)) ∨ True) ∨ p1) → p5))) ∧ (p4 ∨ True))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601376694126069288213806687990 : ((((p2 ∧ (p5 ∧ ((p2 ∨ (((p4 ∨ True) → (p4 ∨ ((((p2 ∧ p5) ∧ p5) ∧ p2) ∧ (p5 ∨ (True → p3))))) → p5)) ∨ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784379676314725227620686200895 : (((p3 ∨ (p3 ∧ (((((False ∧ False) ∧ True) ∧ ((p2 → (p3 ∨ (p4 → p5))) → (False ∧ p4))) ∧ p1) ∨ (p4 ∨ (p1 ∧ (True → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481107182225000536281578374460 : (((((True ∧ p2) ∨ (p3 ∨ ((True → p3) ∨ False))) ∨ ((True ∨ True) ∧ ((((p4 ∨ (True → True)) ∨ p2) → ((p2 ∧ p5) ∧ False)) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39647702552101871939321351567 : (((p3 ∨ (((p1 ∨ ((False → False) ∧ (p4 → p1))) ∨ (p1 ∧ p4)) ∨ (p2 → (p5 ∧ (((p5 ∧ p3) ∧ p1) ∧ (False ∨ True)))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38352706000737464694155894544 : ((((p3 → (p1 ∨ ((((((p3 → p4) ∨ True) ∨ (p1 ∨ p2)) → p1) ∨ p5) ∨ p5))) ∧ (p2 → ((p3 → p1) ∨ (p2 ∧ p5)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689713897810572598388530025221 : ((((((False ∧ p3) → p1) ∧ ((p1 ∧ (True → p3)) ∨ ((False → (p5 ∧ p4)) ∧ False))) ∨ (((p4 ∧ (p4 ∨ (False → p4))) → p2) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208053876300177846644458502710 : (((False ∨ (p4 → False)) ∨ (p5 ∨ p1)) → (((((False ∧ ((p1 ∨ (p1 → (p4 ∧ (p5 ∨ p5)))) ∨ (p2 ∧ p5))) ∨ True) ∨ p1) ∨ p4) ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40387005976673455424565412063 : (((((False ∧ (True → (((((p5 → p2) → ((p3 ∨ p2) → p2)) ∧ p4) ∧ p2) → (p3 ∧ (p5 → p1))))) ∨ (p1 → True)) ∨ p5) ∨ p1) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649560182059124587845391881069 : ((((((p5 ∧ (((p5 → False) ∧ p2) ∨ ((((p3 ∧ (p5 → p2)) ∧ p5) → (p4 ∨ p1)) ∧ p4))) ∧ p4) ∨ (p5 → p5)) ∧ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172627055745720939979899978416 : (((p2 ∧ p5) ∧ (((p3 → p3) ∨ ((True ∨ (p1 ∧ (p5 → p2))) → False)) ∧ False)) ∨ (((True ∧ (False ∧ (False ∧ False))) ∨ (False → True)) ∨ False)) := by
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
theorem thm_5_vars_149221926175398863041503619699 : (((p2 ∧ p5) ∨ (((False → ((p1 → (((p2 ∨ False) ∨ p4) ∧ p5)) ∧ True)) → (p1 ∧ False)) ∨ (True ∨ p4))) ∨ ((p1 ∧ p1) ∨ (p4 ∨ p5))) := by
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
theorem thm_5_vars_116485678331816807223241030517 : (((p2 ∧ p1) ∧ ((((((p5 ∨ (True ∨ (False ∨ p2))) ∧ p4) → p2) ∨ (p4 ∨ (p3 → (p2 ∧ False)))) ∨ p5) ∨ (False → True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256838288829055968147419795671 : ((p1 ∨ p3) → (((((p4 → (False ∨ ((False ∨ (p2 → (p2 → p1))) → False))) ∧ (p3 ∧ p2)) → p1) → p3) ∨ (p4 ∨ ((p2 ∧ True) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118559061927618784164408769305 : ((p3 ∨ (p5 → ((p5 → (((p2 ∨ (((p3 ∨ (True ∧ p5)) ∧ p1) ∧ p2)) ∨ p2) → ((p2 → (p4 → p2)) → p4))) ∨ p5))) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199508058869472307100123739188 : (((p2 → (p2 ∧ ((True → p5) ∧ p3))) ∨ False) → (((p2 → ((True → p5) ∧ (p2 → (p5 ∧ (((p4 → p4) ∨ True) → False))))) ∨ p5) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226025695151358071887146136827 : (((p4 ∧ p4) ∨ p3) ∨ (((p4 ∧ (False → ((((p5 ∧ (True ∨ (True ∧ False))) ∧ (p2 ∧ False)) ∧ p4) ∨ p3))) ∨ p3) ∨ (p5 → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126006163500219329128474866267 : (((False → False) → ((p1 → ((p5 ∧ (((p4 ∧ p1) → ((p3 → (p3 → False)) ∧ p4)) → ((p1 → p1) ∧ p4))) ∧ p1)) ∧ p3)) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158928603348353096637051929560 : ((p2 ∨ (((((p2 ∨ (((p3 → True) → False) → p4)) → p2) ∧ (p4 → True)) ∧ (True ∨ p1)) ∧ False)) ∨ ((p2 ∧ p4) → ((p5 ∨ p4) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171616688464218241857873956757 : ((((p5 ∧ (p2 → (p4 ∧ p1))) → ((p1 ∧ p1) ∨ (p2 ∧ (p4 → False)))) ∨ p5) ∨ (((p3 → True) ∨ (p2 ∨ p2)) ∨ (False → (p4 ∨ p4)))) := by
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
theorem thm_5_vars_192179381370457883965510013656 : ((((((True ∧ (True ∧ True)) ∧ p2) → True) ∨ p2) ∧ p4) → (((p3 ∨ ((((p1 → p1) → (p5 ∧ p1)) ∧ (True ∧ p4)) ∧ p4)) ∨ True) ∨ p1)) := by
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
theorem thm_5_vars_38278439997923698642877240000 : (((((((True ∨ p5) → p5) → ((p2 ∧ (p1 ∨ p1)) ∨ (p3 → False))) ∨ ((p5 ∨ False) ∨ p4)) ∨ ((True ∨ p2) ∨ (False ∨ p3))) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



