variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55965189135856897115649665613 : (((((False ∧ p2) ∨ False) ∧ p2) ∨ ((True ∧ (False → ((((p2 ∧ (((p3 ∨ True) ∧ (p5 ∨ p5)) ∨ p4)) ∨ p1) ∧ False) ∧ False))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322367306844799265539780351096 : (p5 ∨ ((((((p2 → p3) ∨ p1) → ((((p4 ∧ (False ∨ (p4 ∨ False))) ∨ p4) ∨ p4) ∨ True)) → p5) ∧ ((p2 → p1) ∨ (p4 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212236983589363949090064231694 : ((False ∨ ((p5 ∨ False) → p5)) ∧ ((p3 → (p4 → ((p4 → (((True ∨ ((p2 ∧ p5) → (p5 ∧ p4))) → p2) ∨ p4)) ∨ p2))) ∨ (True ∨ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217209249094453500845499038633 : ((((True → p1) → p1) ∨ p5) → ((p1 ∧ p3) → (p1 → (((((((p2 → (p4 → (p2 → p3))) → p5) → p2) → False) ∨ p2) ∧ p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299036925787128053968577828701 : (False ∨ ((p5 ∨ (((p2 → (False ∨ ((p4 → p4) → (p3 ∨ False)))) ∨ ((p5 → (p2 ∧ (p2 ∧ (p4 ∨ (p2 → p4))))) ∨ p4)) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_209146507759349392218252245705 : ((p3 ∨ ((True → (p5 → True)) → True)) → (((((False → p5) ∨ False) ∧ (p4 ∨ (p4 → p3))) → p3) ∨ (((p4 ∨ p4) ∧ p3) → (p3 ∨ p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204978660029919273830103022461 : (((p3 ∧ ((p1 → p3) ∨ p5)) → p1) ∨ (p3 ∨ (((p5 ∨ (((p2 ∧ p3) ∧ p4) ∨ (p4 ∨ True))) ∧ p3) ∨ (True ∧ ((False ∨ p2) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54023176982430937990727078634 : (((((True → (p1 ∨ (False → p2))) → p3) ∧ (True ∨ True)) → (((p4 ∧ (p4 ∨ p5)) → (p4 ∧ ((p3 ∧ p5) ∧ p5))) → (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44596593510286321459298433146 : ((((((p1 ∧ p2) ∧ ((p4 → p5) ∧ p2)) ∨ p1) → ((((True ∧ p4) → False) ∨ p1) ∨ (p4 → (((p2 ∨ p5) ∧ False) → p2)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116520107696774065960020087833 : (((p5 ∧ p2) ∧ ((True → (p2 ∨ (((((p4 → False) → p4) → p2) ∧ ((p5 → True) → (p3 ∧ p1))) → (True → p5)))) ∨ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134057440496476526127576497852 : ((((p1 → (((p1 ∨ (p4 ∧ True)) ∨ p5) → ((p1 → ((True ∨ ((False → p5) ∨ True)) ∨ p2)) ∧ False))) ∨ p3) ∨ p2) ∨ (p5 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177682081912276522379863659919 : ((((p2 ∧ (True ∧ ((p3 → (False ∧ (False ∨ False))) → False))) → False) ∧ False) ∨ (((False → (p2 ∧ ((p4 ∧ True) ∨ False))) ∨ (False → False)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349475767537978556570422007260 : (p3 → (p5 → ((((p4 → p3) ∧ (p3 → p5)) → (True ∧ ((p1 ∧ False) ∨ ((p5 ∧ p1) ∨ p2)))) ∨ (p2 → (True ∨ ((p2 → p3) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41542969424398725304888404211 : (((((p1 ∨ True) ∧ ((False ∧ p3) ∧ (False → (True → True)))) ∨ (p1 ∨ ((((p2 ∧ p5) ∧ p1) ∧ (p3 ∨ (p5 ∧ False))) ∧ p2))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164331853808481536902672972723 : ((p2 → ((p1 ∧ p4) ∨ ((((p2 ∧ p1) ∨ (p4 ∧ p5)) ∨ (p2 ∧ (p3 ∨ p2))) ∨ p1))) ∧ ((False ∨ p2) → (p4 → ((False ∧ p4) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58026263695140175974774070864 : (((True ∧ p3) ∧ ((False ∨ (p3 ∧ p3)) → ((((((p3 ∧ p1) ∧ p1) ∨ (False → ((p5 → (p1 ∧ p1)) ∨ p5))) → False) ∧ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714742506211213574900275499393 : ((((True ∧ (p2 ∧ ((p1 ∨ p4) ∧ p1))) → (p4 ∧ ((((p2 ∨ False) → p1) ∧ p2) ∧ (p3 ∨ ((True → ((p4 → False) ∧ p1)) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611061866369294868111627730274 : ((((((((False ∨ True) ∨ False) ∨ p5) ∧ (((((p5 → p5) ∧ False) → p2) ∨ (((p4 → p2) → (p4 ∧ p2)) ∧ p5)) → p3)) → p4) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_2504476877914935824832805831 : ((False → ((p1 ∨ (p1 → p5)) → ((p4 ∧ p2) ∧ p2))) → (((True ∧ p2) ∧ ((True ∨ p5) → p3)) ∨ (False → ((p5 ∧ p5) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633004407620215513352343498408 : (((((((True ∨ p3) ∧ (p3 ∨ ((p3 ∧ p3) ∨ p3))) ∧ (((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) → False)) ∧ (False → p1)) → False) ∨ p1) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h10
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h19
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h25 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h26
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h29 := h5 h25
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h31 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h32 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
        -- Implications on the right can always be decomposed.
        intro h33
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h36 := h5 h32
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h41 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h42
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h44
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h45 := h5 h41
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h47 : ((p2 ∧ p4) → (p4 ∨ (False ∨ (p3 ∧ p5)))) := by
          -- Implications on the right can always be decomposed.
          intro h48
          -- Conjunctions on the left can always be decomposed.
          let h49 := h48.left
          let h50 := h48.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h50
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h51 := h5 h47
        -- False on the left can always be used.
        apply False.elim h51
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1495185056739114924893743788 : ((((((p4 ∨ True) → p4) ∧ (p5 ∧ ((((True ∧ p3) → p1) → p3) ∨ (p2 ∧ False)))) ∧ (p4 ∨ p5)) → (p5 → p4)) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197802313854290442416948219630 : ((((False ∨ p1) ∨ p1) ∨ ((p1 ∨ p5) → False)) ∨ (True ∨ ((True → p2) ∨ (p2 ∧ ((False → (p1 ∧ p3)) ∧ (p3 ∨ (p2 → (p3 → False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111852522097906465923869413833 : (((((p1 ∨ p1) ∨ ((p5 ∨ ((p1 ∨ (p3 ∧ ((p5 ∨ p5) ∨ True))) → p1)) → (p2 ∧ p5))) → (p3 ∨ (p4 → p5))) ∨ p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756564107756816060834678058177 : (((p1 ∧ (((p4 ∧ (False ∨ ((p2 → ((p1 ∧ (p4 ∧ (True ∨ p3))) ∧ p5)) → False))) → p4) ∧ (((p1 ∧ (p5 ∨ p1)) → p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303278389868355036578990616551 : (False ∨ (p5 → (p5 → ((p2 ∨ (((p4 ∧ (p4 → (p4 ∧ (p2 → (p2 ∧ p5))))) ∨ p1) ∧ (((p2 ∨ p3) ∨ False) ∧ (p3 ∨ p4)))) ∨ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704557667633810155423262436684 : (((((True ∨ p4) ∨ (((True → (p2 ∨ False)) → p2) ∧ False)) → (((False → ((p5 ∨ p1) → p3)) → (False ∨ False)) → (p2 ∧ (p2 ∨ p4)))) ∨ p4) ∧ True) := by
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
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (False → ((p5 ∨ p1) → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h5
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (False → ((p5 ∨ p1) → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h14
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- False on the left can always be used.
    apply False.elim h24
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : (False → ((p5 ∨ p1) → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h28
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h32 := h2 h27
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
    case inr h35 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- False on the left can always be used.
    apply False.elim h38
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182768418755081620841317631988 : ((((True → (p5 → p4)) ∧ False) → ((p5 → p5) → (p4 ∨ p1))) ∧ ((((p3 ∧ ((p4 ∧ (p5 → p3)) ∨ p2)) ∨ p2) ∨ (p3 ∨ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797349572330371306059034827851 : (((p1 → (((p4 ∨ (((p5 ∧ (p5 ∨ p1)) ∨ p2) ∨ (p3 ∧ p5))) ∨ (((p3 ∧ (False ∨ (p3 ∧ (p2 → p3)))) → p1) ∨ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122215987852636608506497853442 : ((((p1 ∧ ((p4 ∨ (((p4 ∨ p1) ∨ p1) → p2)) ∨ p4)) ∨ (p2 ∧ ((p1 ∨ (p1 ∧ (p4 ∧ p1))) ∧ p2))) ∧ (p4 ∨ p5)) → (False ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
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
        -- Disjunctions on the left can always be decomposed.
        cases h3
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593037569675162605110472214489 : (((((((((((p5 ∧ p5) ∧ p4) ∨ (p4 → False)) ∧ (False → False)) → p5) → ((p2 ∨ False) → p3)) ∨ p4) ∨ ((p5 → True) ∧ True)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249525014396576160016430493715 : ((p5 ∨ p1) ∨ (p5 → (((p4 ∨ False) ∨ ((((True → False) ∧ ((p4 ∧ False) → p5)) → (p2 ∧ (((False → True) ∧ p4) ∧ p5))) ∨ False)) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111120903928684251400411611978 : (((((False ∨ ((p4 ∧ (p3 ∧ p1)) ∧ p4)) → p1) ∧ (((((p3 ∨ (p3 ∧ False)) → True) → p1) → p4) ∧ (False ∨ p3))) ∧ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158864363956693477988901407738 : ((False ∨ ((p2 ∧ ((((p5 → p3) → p5) ∧ (p5 ∧ (p3 ∨ (p5 ∨ p3)))) ∧ True)) ∧ (False ∧ p3))) ∨ (True ∨ (p3 ∨ (False ∧ (p2 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133667955412948720797003097174 : (((((p4 ∨ (((((True ∨ p1) → True) ∨ (((p3 → p4) ∨ p1) → p3)) ∧ p3) ∨ p2)) ∨ p1) → (p1 ∨ p4)) ∧ False) ∨ (p4 → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198049234487461259888540095294 : (((p3 ∧ p4) ∨ (False ∧ (True ∧ (p2 ∨ p4)))) ∨ (((p5 → (p5 ∨ p1)) ∧ ((False ∨ p4) → (True ∨ ((p1 ∧ (p1 ∨ True)) ∧ p3)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787691404979919767969674625089 : (((p4 ∨ (p4 ∨ (p2 → ((((True ∨ False) → p1) → (((p3 ∨ (p1 ∨ True)) ∧ (p4 ∨ (p4 ∨ p2))) → (True → False))) → (p4 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189026694955915768952940641217 : (((False ∨ (p3 ∨ p4)) ∨ (p4 ∨ ((p5 ∨ False) → p5))) ∧ ((((False ∨ p4) ∨ False) → p5) ∨ ((p5 → (p5 ∨ (p3 ∨ p4))) ∨ (False → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197436454320540836298248985917 : ((((False ∧ (p5 ∧ p4)) ∧ p3) ∧ (p4 ∨ p3)) ∨ ((p3 ∨ (False ∧ True)) ∨ (((False → ((p2 → (p1 ∨ p4)) → False)) ∧ (False ∧ p2)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300682925508155022583686285228 : (False ∨ (((False → (p1 ∨ (False → p4))) → (p5 ∧ ((p5 → False) → (p5 ∨ (p2 → (p1 → True)))))) ∨ (((p5 → p5) → p3) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_792599219588623267447555477234 : (((True → ((True → (((p2 ∧ (p4 → False)) → p2) ∧ False)) → ((p1 ∧ (p4 → (((p2 ∨ (p3 ∨ p1)) ∧ (p3 ∧ True)) → p3))) ∧ p4))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h9.left
      let h16 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h9.left
      let h19 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h18
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h20 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h21 := h2 h20
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- False on the left can always be used.
  apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52694438032895651155471953553 : (((p1 → ((((p1 → (p1 ∧ ((p3 ∧ p2) ∨ p5))) → False) ∨ p3) ∧ p4)) ∨ ((((False → False) ∨ True) ∨ (p5 ∨ (False ∨ p5))) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_625034205906646918351108967877 : ((((True → (((p3 ∨ p1) ∨ ((p1 ∧ ((True → p4) → (((p5 ∧ p4) ∧ (p1 ∨ p3)) ∨ (p1 ∨ (p4 ∧ True))))) ∧ p3)) ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173059048344746233376972259677 : ((False ∨ ((((p5 → p4) ∧ (True ∨ p5)) ∧ p2) → ((p3 ∧ p3) ∧ (False → p2)))) ∨ (p5 ∨ (p3 → (((False ∧ p5) ∨ True) ∨ (p3 → p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301925413411718621658131115866 : (False ∨ ((True ∨ True) → (((p1 ∧ ((False → (p2 → (p5 ∧ True))) → False)) → False) → ((False → False) ∧ ((((p1 ∨ p3) → p2) ∨ p5) ∨ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
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
theorem thm_5_vars_132683989259866615633240423413 : ((False ∨ ((((p3 → p2) ∧ (False ∧ (p1 ∧ True))) ∧ False) ∨ (p4 ∨ (True ∨ ((p1 ∧ (True ∨ False)) ∧ (p2 ∨ p4)))))) ∧ ((False ∧ False) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724190200178089125211978906022 : ((((p3 ∧ (p3 ∧ p4)) ∧ (((p4 → ((p3 ∧ False) ∧ (p2 ∨ ((p5 → (p4 ∧ (False ∨ (p5 → (p1 ∧ p1))))) → True)))) → True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336266421954678332492561839109 : (p1 → ((((p3 ∧ ((True ∧ (((p4 ∧ p1) ∨ p1) ∨ p2)) → (p1 → False))) ∨ p2) → (((p3 ∧ (False ∧ (p5 → p1))) ∧ p5) ∧ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624471753830085888676629974189 : ((((p4 ∨ ((((((p3 → (True → (True ∨ p2))) ∨ True) → p4) ∨ (p1 → ((p5 ∨ ((p1 ∨ p2) ∨ True)) ∧ True))) → p5) ∧ p4)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_207753824389526470332994682004 : (((False ∨ (p4 ∨ (p3 ∧ p4))) → p3) → ((p1 ∨ ((p4 ∧ p5) ∧ p5)) ∨ (p1 → ((p5 ∨ p5) ∨ (((p1 ∨ (p4 → p1)) ∧ p3) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151031299949120476213319576242 : (((((((p5 → p2) ∨ (p4 → p2)) ∨ (p2 ∨ ((p3 ∧ p2) → ((p5 ∧ p3) → p1)))) ∨ p3) ∧ p5) → p4) → (((p2 ∧ p4) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157136368952770715793889441155 : ((((p2 ∨ (p3 ∧ ((True ∧ ((p5 ∧ False) ∨ False)) ∨ ((p5 ∧ (p5 ∨ False)) → False)))) ∧ p1) → p5) ∨ (p2 → ((p4 ∨ (False ∨ p2)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299366862353023914478991688062 : (False ∨ (((False ∧ p2) ∨ ((((p4 ∨ p2) → True) → (((p5 → (p1 ∨ ((p3 ∨ p1) ∧ False))) ∨ (False ∧ p5)) ∧ (p3 ∨ p4))) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614058852949005568504975644916 : (((((p2 ∧ (((p1 ∨ ((((p1 → p5) → p4) ∨ p2) ∨ p4)) ∨ (p4 ∨ p5)) ∧ ((False → p2) ∨ p2))) ∨ ((p1 → p1) ∧ p1)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_221148213107411988530209315713 : (((True ∨ p5) ∨ False) ∧ (((p1 ∨ p5) → (p1 ∧ False)) → (((False → (p5 ∧ ((p2 → False) → False))) → False) ∨ (p1 → ((p3 ∧ p3) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54481406443451040674248508531 : ((((False ∧ ((False ∧ p2) ∨ p1)) ∨ (p5 ∨ p3)) ∨ (p4 ∧ ((p5 ∧ p4) → (p3 ∧ (p4 ∧ (p1 → (((False ∧ p5) → False) → p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338817847665030276020750846161 : (p1 → ((p3 ∨ p4) ∨ (((p2 → (p3 ∧ ((p2 ∧ (True → p2)) ∧ p3))) → ((p1 → (p1 ∧ (p3 ∧ p5))) ∨ (p2 → (p3 → True)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773494016433985895685815758888 : (((False ∨ ((((p2 ∧ p4) ∧ (((p1 → p2) → (p1 ∨ (p4 ∧ (((False ∨ False) → p2) → (True ∨ p3))))) ∨ True)) ∨ (True ∧ p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41962584948270352010165641480 : ((((p5 ∧ p1) ∧ (((True → (p2 ∨ ((((p2 → ((True → (p5 ∨ p5)) ∧ True)) ∨ p2) ∨ (False ∨ p5)) → p3))) ∨ p5) → p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950142726849955312843156116626 : (((((p3 ∨ False) → p4) ∧ (((True ∧ (p3 ∧ ((((((p4 → p5) ∨ False) ∨ p3) ∨ (p1 ∧ p5)) → False) → (True ∧ p3)))) ∨ True) → p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ (p3 ∧ ((((((p4 → p5) ∨ False) ∨ p3) ∨ (p1 ∧ p5)) → False) → (True ∧ p3)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180121015456818403453824701415 : ((((p3 ∨ (p1 → (((p5 ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ p1) → False) → ((False ∧ ((((p5 → p5) → p5) ∨ p1) ∧ True)) ∧ (p1 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (p1 → (((p5 ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∨ (p1 → (((p5 ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∨ (p1 → (((p5 ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ p1) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : ((p3 ∨ (p1 → (((p5 ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228051724993900461778779881366 : ((p4 ∧ (False ∧ p5)) ∨ ((p2 ∧ (((p4 → p4) ∨ ((p5 → p1) ∨ p2)) → False)) ∨ (((False ∨ (p1 ∧ False)) ∨ (p1 → (p2 ∨ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199351656475124299814888726229 : ((((False → (p5 ∨ (p3 ∨ False))) → False) ∨ False) → ((p5 ∨ ((p1 ∨ (False ∨ p5)) ∧ ((p3 ∨ p2) → (p5 ∨ ((p5 ∨ True) ∧ p3))))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False → (p5 ∨ (p3 ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (False → (p5 ∨ (p3 ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50993155629908771442039526216 : ((((p4 → True) ∧ ((((p4 ∨ (p1 ∧ (False → p3))) ∨ (p5 → (p2 ∧ p4))) ∨ p2) → p3)) ∧ (((False ∨ p4) → (p3 ∨ p5)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92747364090517996632592279238 : (((p3 → p3) → (((p2 ∧ (((p4 ∧ p1) ∨ ((p1 ∧ (p2 ∨ p2)) → False)) ∨ False)) ∧ ((p1 → (p3 → False)) ∨ p2)) ∧ (p3 ∧ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141271910147524740436592059459 : (((((True → p3) → p3) ∨ False) ∧ (p2 ∧ (p2 ∧ (p5 → ((((p3 → p4) ∨ p1) ∧ p2) ∧ ((p4 ∨ p5) ∨ p2)))))) → ((p4 ∨ True) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228050048801569229037384816431 : ((p4 ∧ (False ∧ p3)) ∨ ((p5 → ((((p3 ∧ True) → p2) → p2) → (p5 → (False → ((p2 ∧ p4) → p2))))) ∧ ((p4 ∨ (p1 ∨ True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218542741904901586102809193357 : (((p5 ∨ p4) → (False ∨ p4)) → ((p1 → True) ∧ (p3 → (p2 ∨ (p3 ∧ ((p4 → p2) ∨ (((False → p2) ∨ (p2 ∧ False)) ∧ (p4 ∨ True)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149391445199073060705029837025 : ((True ∧ (((((p1 ∨ (((p1 ∨ (False ∧ (p3 ∧ p4))) ∧ p2) ∧ (True ∧ False))) ∨ True) ∧ p4) ∧ p2) ∧ p5)) ∨ (p3 → ((p1 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46355326425342847168081274785 : ((((True ∨ ((p3 ∨ False) ∨ ((p5 → False) ∧ (p2 ∨ (p4 → (p2 → True)))))) → (((p4 → p5) ∨ (p2 ∨ p1)) → p2)) ∧ (p1 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117686023786085444186854961663 : ((p3 ∧ (((p1 ∧ True) ∧ p1) ∧ ((p1 → p2) ∨ (((p5 ∨ ((p1 ∨ (True ∧ p3)) ∧ True)) ∧ False) ∨ ((p2 ∧ p2) ∧ True))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335706936772273168904668270859 : (p1 → ((((p3 → p4) ∨ (((p1 ∨ True) → ((p4 ∨ ((p5 ∨ p4) → (True → (p3 ∨ (True ∨ p5))))) → (True ∧ False))) ∨ True)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47700437016387340323627103663 : ((((p3 → (((((True → ((((p2 → False) → ((p1 ∨ p3) ∨ p5)) ∨ True) → p5)) ∨ p2) ∨ False) → p4) ∧ p3)) ∧ p2) → (p4 → p4)) ∨ p5) := by
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
theorem thm_5_vars_683438901290966718687583024014 : ((((p1 → ((((((p1 ∨ p3) ∧ (False → p3)) ∧ False) ∨ False) ∧ p4) → (p4 ∨ (p2 ∧ p2)))) ∧ ((p4 ∨ p2) ∧ (p5 ∨ (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151639079948905778426668529562 : ((((p2 → (((p4 → False) → p1) → ((True ∧ (p5 → (p1 ∧ p5))) ∧ p4))) ∧ p3) ∧ (p5 ∨ (p2 → p5))) → ((p1 ∧ (True → p5)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125371836633166607862333980839 : (((p4 → (p4 ∨ p1)) → ((p1 ∧ (p4 ∨ (((p1 ∧ ((p1 → True) ∧ (p4 → p1))) ∨ False) ∨ p4))) ∧ (False ∧ (p1 ∧ p4)))) → (p2 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (p4 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → (p4 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115107047289170552924426661427 : (((((False → False) ∨ (((p1 ∨ (False ∨ p4)) ∨ True) → p2)) ∨ p3) → (((((True ∨ p3) ∧ (p4 → False)) ∧ p4) → True) → p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657707425141552894231033074626 : (((((p3 → False) → (((p4 → p5) ∧ (p1 ∧ ((p5 → ((False → (p5 ∨ p2)) → p3)) ∨ (p3 ∨ (p4 ∧ p1))))) ∨ False)) ∨ (False → p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_133639454987638385542845021801 : ((((p3 → (p2 ∧ ((p4 ∨ p3) → (((True ∨ (((False ∨ p3) ∧ p5) ∧ p1)) ∧ False) ∧ (False → p4))))) → p5) ∧ False) ∨ ((p1 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658108967416035730291903014074 : ((((p3 ∧ (p1 → (((((((p4 ∧ p1) ∧ (p4 ∨ p1)) → False) ∧ (p1 ∧ p5)) ∨ p2) → p2) ∧ ((p3 → False) → p3)))) ∨ (False → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739431690391040973744071049550 : ((((p5 ∧ True) ∨ ((p2 ∧ p1) → ((((False ∧ (p4 → (False ∨ (p2 → p4)))) ∨ (p1 → False)) ∨ (p1 → p5)) → ((p4 ∧ p5) ∨ p1)))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672901289251489691547923530965 : (((((((True → p1) ∧ (((p2 ∨ (True ∨ p4)) → ((p3 ∧ True) ∨ p1)) ∧ p3)) ∨ p4) → ((p4 ∧ True) → p1)) → (p1 ∨ (False ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166444702526944316004546827125 : ((p2 ∨ ((((p5 ∨ (p5 ∧ ((p3 ∨ p3) ∧ ((p4 → True) → p5)))) → p2) ∧ True) → False)) ∨ (((p3 ∨ p4) → (True ∧ p5)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_165455698358966478881083851185 : ((((p1 ∧ ((p5 → (p3 ∧ p5)) ∨ p2)) → (p5 ∧ p2)) ∧ (((p5 ∧ p3) ∨ p3) → False)) ∨ ((p1 ∨ (((p2 → p3) ∨ p1) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317950777173134928642720905625 : (p4 ∨ ((p4 ∨ ((((((p1 → p3) ∧ True) ∧ p5) ∨ p3) ∨ p1) → (p2 → (False ∨ ((True ∨ p4) ∧ (((p3 ∧ p5) ∨ p3) → p3)))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42963575455292237543135535477 : (((p5 → (((p4 ∨ (((p1 → True) → p4) ∨ ((False → True) ∧ p4))) → (((True → p4) ∨ (p4 → (p3 → p1))) ∧ p2)) ∨ p2)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113309793747579994682033449022 : (((((p3 ∨ (False ∨ p2)) ∧ p4) → (False ∧ (((p1 ∧ p5) ∨ ((False ∧ (False ∧ p2)) ∧ p3)) ∧ (p2 ∧ p3)))) ∧ (p4 ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137338010006445233176241947281 : ((p2 ∧ (p4 ∨ (True ∧ (((((p1 ∧ p3) ∨ p1) ∨ p5) ∧ (p2 ∨ (p5 ∧ ((p2 ∨ (False → p3)) → p2)))) ∨ False)))) ∨ (p1 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164773400527064795844878701363 : ((((p3 → ((p5 ∨ p4) ∨ ((p3 ∨ p1) ∧ p1))) ∨ (p3 ∨ (True → (p5 ∧ p4)))) ∨ p4) ∨ (p1 → (((False → p5) ∧ (p5 → True)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41767876397937429501108869746 : ((((p3 ∧ (p2 → (False ∨ p5))) ∨ (((((p4 ∨ (False → p4)) ∨ ((p4 ∨ p1) ∨ True)) → p4) ∧ (p1 ∨ p4)) ∧ (p4 ∨ True))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336221086138575580668138681940 : (p1 → ((((p5 → p1) → (((p3 → (p1 ∨ p4)) ∧ False) ∨ (((p2 ∨ p4) ∧ (True → True)) ∨ (p4 → p3)))) ∧ ((p4 ∧ False) ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166105225568367056253994224599 : (((p3 → p1) → (((p3 ∨ (p4 ∨ (p4 ∧ False))) ∧ p2) ∧ (False ∨ ((False ∨ p2) → True)))) ∨ ((p1 ∨ (p5 ∧ (p1 ∧ p5))) → (p2 → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231722553259796942593205354231 : (((p2 ∧ p2) → p4) → ((p1 ∨ (((False → p3) → (((p1 ∧ (p2 ∧ False)) ∧ (False ∨ False)) ∧ (p5 → (p2 ∨ (p4 → p3))))) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194706439444133096494712903408 : ((((p4 → True) ∨ (True ∨ (p3 → p2))) ∨ True) ∧ ((((p2 → (True ∨ False)) → ((p1 ∨ (((p2 → p2) ∨ p5) ∨ p5)) → p5)) ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_197667950720121764990882984884 : ((((p3 ∧ p4) → (True ∧ p4)) → (False ∨ p5)) ∨ (True ∨ (p2 ∧ ((False → ((True ∧ (p1 ∨ True)) ∧ ((p3 ∧ p5) ∨ p4))) ∨ (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205913619936715473349809238201 : ((True ∧ (p5 → ((p3 ∧ p5) ∨ p4))) ∨ ((p2 ∨ ((p1 ∨ True) ∧ p2)) ∨ (p3 ∨ (False → (p3 → ((((p5 ∧ True) ∨ True) ∨ p3) ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323542119623481438667903554350 : (p5 ∨ ((((False ∨ ((p3 → p3) → (((p2 → False) ∨ (False → p3)) → p4))) → (p2 ∧ ((False → False) → False))) ∨ p1) → ((p2 ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616948985016410859165883273037 : (((((p2 ∨ (p1 → (False ∧ (((p2 ∧ p1) ∧ p5) → p1)))) → (p4 ∨ (((p5 ∨ p5) → p5) ∧ ((False ∧ False) ∨ (p5 ∨ False))))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_51554942773565032641522531135 : (((p5 ∧ (((p2 ∨ (False ∧ (p5 ∨ p4))) → ((True ∧ p4) ∨ (p2 → p5))) → (p1 → p5))) → (p2 ∧ (p1 ∨ (p1 ∧ (p2 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113446267107632626299468320134 : ((((p5 ∧ ((False ∧ (p1 ∧ (True ∨ (((p4 ∨ (False → p2)) → (p4 → (True ∨ True))) ∧ False)))) ∧ p5)) ∨ p4) ∨ (True ∨ p3)) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111921458029101350244144604312 : (((((((p3 ∧ (p1 ∨ p3)) ∧ (p4 → False)) ∨ True) ∧ (p3 ∨ p5)) → (p3 ∨ ((((p5 → True) ∧ p2) ∨ False) ∨ p3))) ∨ p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



