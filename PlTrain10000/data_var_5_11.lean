variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662142304670068366194174710425 : ((((((p3 ∨ (((p5 ∨ (p2 ∧ p4)) ∧ p3) → True)) ∧ (p1 ∨ True)) → ((p3 ∨ (p1 ∨ ((True ∨ False) → False))) ∧ p3)) → (p3 ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (((p5 ∨ (p2 ∧ p4)) ∧ p3) → True)) ∧ (p1 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134534453154917593183111984519 : (((((p3 ∧ (((((p2 ∨ p3) → ((p1 → p4) → (p4 ∧ (True ∨ p4)))) → p5) ∧ p3) ∧ p3)) → p2) → p1) → p2) ∨ (p2 → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180531093354714663867222424093 : (((((p3 ∧ (p1 → p2)) ∨ p2) ∨ (p5 ∨ p1)) ∨ (p1 → (True ∨ False))) → (p2 → ((p1 → p4) → (True → (True → (p3 → (p1 → p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h17 := h3 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h20
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h24 := h3 h23
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h26 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h27 := h3 h26
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688081273429048058045838663759 : ((((((p4 → False) → (p3 → False)) ∨ (True → ((True ∧ False) ∨ ((p4 ∨ p4) → True)))) ∧ ((p5 → ((p1 → p4) ∧ (p2 → p1))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758951652497410486483636145200 : (((p2 ∧ (((False → ((p5 ∨ (p3 ∨ p3)) → p5)) ∧ ((False ∨ p1) ∨ ((p1 ∧ ((p5 → p4) → ((p3 ∧ p3) → True))) ∨ p3))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168153027055534340735090861590 : ((((p2 → True) ∧ True) ∧ ((((p4 → True) → p1) ∨ ((p5 → False) ∨ (False ∨ p2))) ∧ p1)) → (((p2 ∨ ((False ∨ False) ∨ p1)) ∧ p4) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65251836555905411110049127280 : ((p3 ∨ ((((p4 → (((((p1 ∧ (p5 → False)) ∧ p2) → p4) ∧ True) → p5)) → (p1 ∨ True)) → ((p1 ∨ (p2 ∨ True)) ∧ p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198070907877958773824186792089 : (((p1 ∨ p3) ∨ (p5 ∧ (p1 ∧ (p5 ∧ p1)))) ∨ (((p2 ∨ (False ∧ ((p3 → p4) ∨ (False ∧ p5)))) ∨ p5) ∨ ((False ∧ (p1 ∧ False)) → p2))) := by
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
theorem thm_5_vars_325938217055071273022226815257 : (p5 ∨ (p5 ∨ (((p2 ∧ False) ∧ ((p5 ∨ (((p2 ∨ False) ∧ True) → p4)) ∨ p3)) ∨ ((p2 ∧ ((True ∨ p1) ∧ p3)) → (p1 → (True ∨ p4)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47516789235551019450611813961 : (((p3 ∨ (((False → (p4 → False)) ∧ (p1 → (((p5 ∨ (p4 ∧ p5)) ∨ ((p5 ∨ p4) ∨ (p2 ∨ p3))) ∨ p4))) ∧ p1)) ∨ (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51462993753390208528225305549 : (((((p2 ∧ p1) ∨ ((p1 ∧ (p3 ∧ (p4 ∨ p2))) → p2)) ∨ (((p4 → p5) → p5) ∧ True)) → (((p2 → p4) ∨ (p3 ∧ p4)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70469283565742550052899483763 : (((((p3 → (((True → False) → (p2 ∧ ((p1 ∨ (p5 ∧ ((p2 ∧ p2) → p5))) → p2))) ∧ False)) ∧ p3) ∧ ((p2 → p4) → True)) ∧ p1) → p5) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112054175024837267174325728796 : ((((False ∧ p5) ∧ ((((False → True) → ((False ∧ (p4 → False)) ∨ ((True → False) ∨ p2))) ∨ p3) → (p3 ∨ (p1 → False)))) ∨ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191682123137115774335082178295 : ((p5 ∧ ((p3 ∨ p5) → (((p5 ∧ p4) ∧ p3) ∧ True))) ∨ (p1 ∨ (p1 ∨ (((p1 → p2) → True) ∨ (p5 ∧ (((p4 ∧ False) ∧ False) ∨ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114635704105238773486304662975 : ((((((p1 → (p3 ∨ p1)) ∨ (p3 ∧ (p5 → (p4 → p4)))) ∧ (p2 → True)) → p4) ∨ ((p1 → (p4 ∧ p2)) → (p1 → p1))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711075525186474771842375675581 : ((((True ∧ ((p4 → p1) ∨ (True ∧ p1))) ∧ (p5 ∧ ((((((p4 ∧ True) → p1) ∨ False) ∨ (p3 → ((False → p4) ∨ p5))) → p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149137850870742426800345876393 : (((p5 ∧ True) ∧ (((p1 ∨ False) ∨ (p5 ∧ (((p5 ∨ p3) ∧ ((p1 → p3) → (p1 ∨ p4))) → p2))) ∧ p2)) ∨ (p1 → (p2 ∨ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58794784552086111030468463392 : (((p5 → False) ∧ (((((True → True) ∨ True) → ((((p2 → p4) → p3) ∧ (p5 ∧ (False → (p2 → p4)))) → p4)) ∧ False) ∨ (p3 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469862252736551660116513421557 : ((((p5 → ((p4 → p3) ∧ (((p1 → p1) → (p1 → (p2 → p2))) → p2))) → (((((p4 → (p5 ∧ p4)) ∨ p5) → False) → p5) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113811375178091479516063697242 : (((p1 ∧ ((False → ((p5 → (p1 ∨ (p3 ∨ (((p2 ∨ (False → p3)) ∧ (False ∨ p5)) ∨ False)))) → True)) ∨ p5)) → (False ∧ p5)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2523526517317909679541894719 : (((p5 ∨ (p1 → True)) ∨ (p4 → (p2 → p3))) ∧ (((((False → p2) ∨ True) ∨ p1) ∧ p5) → ((p3 ∨ (p1 ∨ (p1 ∨ p3))) ∨ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340858883567735246882811750646 : (p2 → (((((False ∨ (True → ((p2 → p3) → ((p2 ∧ (p4 ∨ (False ∨ False))) ∧ p4)))) ∨ False) ∨ True) ∧ (p4 ∧ (p3 ∨ (p3 ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59150783472008488373607792013 : (((False ∨ False) ∨ (((p2 → True) → False) ∨ (((((((True → (p2 ∧ (p4 ∧ p1))) ∨ p4) ∧ False) ∨ (True ∨ False)) ∧ False) ∧ p3) → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264862851333978120598889740111 : (True ∧ ((True → False) ∨ ((p5 ∨ (p5 ∨ ((((p2 → False) ∧ p2) ∧ ((p5 → ((p5 ∨ (p4 ∨ p3)) → (p4 ∨ p3))) ∨ p5)) → p3))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52536887081088056055054996959 : ((((p5 ∧ ((p4 ∧ ((p2 → (p1 ∧ p1)) ∧ p4)) → (False ∧ False))) ∨ p4) ∨ (p1 ∧ (((True → p4) ∧ p1) → ((p1 → p3) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173844654453003271745326063213 : (((p2 → ((True → True) → (((True → p4) → (False ∨ (p3 ∨ p2))) ∨ True))) ∨ p4) → ((((p1 ∧ (p1 → (p5 → True))) ∧ p3) ∧ p2) ∨ True)) := by
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
theorem thm_5_vars_764924358968871532463223684626 : (((p4 ∧ (((True ∨ (False → p2)) ∨ (((p1 → (p3 ∨ ((p1 ∧ (p2 ∧ False)) → (((p2 ∨ True) → False) ∨ False)))) ∨ p1) ∧ p3)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330320851582693121424057958807 : (True → (p1 ∨ (((False ∨ ((False ∨ p2) ∨ p2)) ∧ (p1 ∧ p2)) ∨ (p4 → (((((p2 ∨ (True → p2)) → True) ∧ True) ∨ (True ∧ p2)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88133368399930663879627920625 : ((((p2 ∨ p2) ∧ (p1 ∧ p5)) ∧ (((True ∨ True) ∨ p1) ∧ ((((p5 ∨ p5) ∨ True) ∧ ((((p5 ∨ p5) ∧ p1) ∨ p3) → p3)) ∧ p2))) → p3) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h10.left
        let h14 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h19 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h18
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h20 := h16 h19
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h22 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h23 := h16 h22
            -- One of the premise coincides with the conclusion.
            exact h23
        case inr h24 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h25 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h26 := h16 h25
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h10.left
        let h29 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h34 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h33
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h35 := h31 h34
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h36 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h37 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h36
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h38 := h31 h37
            -- One of the premise coincides with the conclusion.
            exact h38
        case inr h39 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h40 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h41 := h31 h40
          -- One of the premise coincides with the conclusion.
          exact h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h10.left
      let h44 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h45 := h43.left
      let h46 := h43.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h47 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h49 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h48
            -- One of the premise coincides with the conclusion.
            exact h42
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h50 := h46 h49
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h51 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h52 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h51
            -- One of the premise coincides with the conclusion.
            exact h42
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h53 := h46 h52
          -- One of the premise coincides with the conclusion.
          exact h53
      case inr h54 =>
        -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
        have h55 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
          -- One of the premise coincides with the conclusion.
          exact h42
        -- We have shown the premise of h46, we can now drive its conclusion.
        let h56 := h46 h55
        -- One of the premise coincides with the conclusion.
        exact h56
  case inr h57 =>
    -- Conjunctions on the left can always be decomposed.
    let h58 := h5.left
    let h59 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h60 := h3.left
    let h61 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h60
    case inl h62 =>
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h63 =>
        -- Conjunctions on the left can always be decomposed.
        let h64 := h61.left
        let h65 := h61.right
        -- Conjunctions on the left can always be decomposed.
        let h66 := h64.left
        let h67 := h64.right
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h68 =>
          -- Disjunctions on the left can always be decomposed.
          cases h68
          case inl h69 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h70 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h69
              -- One of the premise coincides with the conclusion.
              exact h58
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h71 := h67 h70
            -- One of the premise coincides with the conclusion.
            exact h71
          case inr h72 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h73 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h72
              -- One of the premise coincides with the conclusion.
              exact h58
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h74 := h67 h73
            -- One of the premise coincides with the conclusion.
            exact h74
        case inr h75 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h76 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h59
            -- One of the premise coincides with the conclusion.
            exact h58
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h77 := h67 h76
          -- One of the premise coincides with the conclusion.
          exact h77
      case inr h78 =>
        -- Conjunctions on the left can always be decomposed.
        let h79 := h61.left
        let h80 := h61.right
        -- Conjunctions on the left can always be decomposed.
        let h81 := h79.left
        let h82 := h79.right
        -- Disjunctions on the left can always be decomposed.
        cases h81
        case inl h83 =>
          -- Disjunctions on the left can always be decomposed.
          cases h83
          case inl h84 =>
            -- We want to use the implication h82 based on <expert-advice>. So we show its premise.
            have h85 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h84
              -- One of the premise coincides with the conclusion.
              exact h58
            -- We have shown the premise of h82, we can now drive its conclusion.
            let h86 := h82 h85
            -- One of the premise coincides with the conclusion.
            exact h86
          case inr h87 =>
            -- We want to use the implication h82 based on <expert-advice>. So we show its premise.
            have h88 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h87
              -- One of the premise coincides with the conclusion.
              exact h58
            -- We have shown the premise of h82, we can now drive its conclusion.
            let h89 := h82 h88
            -- One of the premise coincides with the conclusion.
            exact h89
        case inr h90 =>
          -- We want to use the implication h82 based on <expert-advice>. So we show its premise.
          have h91 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h59
            -- One of the premise coincides with the conclusion.
            exact h58
          -- We have shown the premise of h82, we can now drive its conclusion.
          let h92 := h82 h91
          -- One of the premise coincides with the conclusion.
          exact h92
    case inr h93 =>
      -- Conjunctions on the left can always be decomposed.
      let h94 := h61.left
      let h95 := h61.right
      -- Conjunctions on the left can always be decomposed.
      let h96 := h94.left
      let h97 := h94.right
      -- Disjunctions on the left can always be decomposed.
      cases h96
      case inl h98 =>
        -- Disjunctions on the left can always be decomposed.
        cases h98
        case inl h99 =>
          -- We want to use the implication h97 based on <expert-advice>. So we show its premise.
          have h100 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h99
            -- One of the premise coincides with the conclusion.
            exact h93
          -- We have shown the premise of h97, we can now drive its conclusion.
          let h101 := h97 h100
          -- One of the premise coincides with the conclusion.
          exact h101
        case inr h102 =>
          -- We want to use the implication h97 based on <expert-advice>. So we show its premise.
          have h103 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h102
            -- One of the premise coincides with the conclusion.
            exact h93
          -- We have shown the premise of h97, we can now drive its conclusion.
          let h104 := h97 h103
          -- One of the premise coincides with the conclusion.
          exact h104
      case inr h105 =>
        -- We want to use the implication h97 based on <expert-advice>. So we show its premise.
        have h106 : (((p5 ∨ p5) ∧ p1) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h59
          -- One of the premise coincides with the conclusion.
          exact h93
        -- We have shown the premise of h97, we can now drive its conclusion.
        let h107 := h97 h106
        -- One of the premise coincides with the conclusion.
        exact h107



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117461737159159675962468038584 : ((p1 ∧ ((p1 ∧ p1) → (((p1 ∧ False) → ((p2 ∨ (((False → (True → p1)) ∨ (p5 → p2)) ∧ True)) → (False → p2))) → False))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164830759617135401120337334866 : (((True ∧ (False ∨ ((True ∧ ((((p4 ∨ True) ∨ p2) ∧ p3) ∧ (p2 → False))) → False))) ∨ p2) ∨ ((((False ∧ False) ∧ p4) ∧ False) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310020154532135226597598478377 : (p2 ∨ ((((p4 ∧ p4) → (False ∨ ((p3 ∨ False) → (False ∨ ((p1 ∧ p2) ∨ p3))))) ∨ p5) ∨ (p3 ∧ ((((False → p1) ∧ True) ∨ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259179377464704137875036228262 : ((False → True) → (p3 → ((((((((p5 ∧ True) ∨ ((True ∨ (False ∨ p4)) ∧ (False ∨ p1))) ∨ (p2 ∧ p4)) ∨ p3) ∨ p3) ∨ p3) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173168489037411196608352295754 : ((p4 ∨ (((((p4 → (p4 ∧ p1)) ∨ p5) → (p2 → p3)) ∧ (p1 ∧ False)) ∨ False)) ∨ (((False ∨ True) → ((p2 ∨ (p4 → p2)) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688011350614247840739854833272 : ((((((True ∨ (p2 ∧ p2)) ∨ (p1 → True)) ∨ ((p5 → ((p4 → True) ∨ p5)) ∨ p2)) ∧ (p5 ∨ (False ∧ (p5 ∧ ((p5 → p2) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338983674459362212536204804325 : (p1 → ((p5 → False) → ((((((((False ∧ True) → p3) ∨ p5) → True) ∨ p3) → p5) ∧ p1) → (p4 ∧ ((p3 ∧ (p2 ∧ p3)) ∨ (p1 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((((False ∧ True) → p3) ∨ p5) → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h3.left
  let h12 := h3.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (((((False ∧ True) → p3) ∨ p5) → True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h13
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h16 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h17 := h2 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669271184951066895742827158016 : (((((p1 → ((p1 ∧ ((p4 → (p3 ∨ p5)) ∨ ((p3 ∧ (p4 ∨ p2)) ∧ False))) ∧ (False → (p4 → True)))) → p2) ∨ ((p4 ∨ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219247008316333451627617389400 : ((p1 ∨ ((True → False) → False)) → ((p4 ∨ ((False ∨ False) ∨ (((p2 → ((True ∧ p1) ∨ (True ∨ (p3 → (True ∧ p5))))) ∧ p2) ∨ p5))) ∨ True)) := by
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
theorem thm_5_vars_42228999677301109238665836165 : (((False ∧ ((True ∧ ((p3 ∨ (p1 → (p5 ∨ p1))) → ((p5 → True) → p5))) ∨ (p3 → (((p2 → p1) ∨ (p2 → p1)) ∨ p4)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228428563733519588268517268349 : ((False ∨ (p4 ∧ p5)) ∨ (((p1 ∧ p4) ∨ True) ∨ ((((p4 ∨ p5) ∧ True) ∧ p5) ∨ ((p4 ∨ p2) ∨ (((p5 ∨ p1) ∨ (p3 ∨ True)) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249192311567670613719220987508 : ((p4 ∨ p3) ∨ ((((p4 ∧ (p4 ∨ True)) ∧ p3) → ((p3 ∨ p3) ∧ False)) ∨ (((p4 ∧ (True ∧ p1)) ∧ p2) ∨ ((p3 ∧ (p2 → p3)) → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305350596279155094640323939236 : (p1 ∨ ((p3 ∧ ((p5 ∨ (p3 ∨ (p2 ∨ ((p1 ∨ (((p4 ∨ p2) ∧ False) ∧ False)) → p1)))) ∧ p4)) → (p2 ∨ ((True ∧ p2) ∨ (p3 ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159213357991130483355599923954 : ((p2 → ((p1 → p3) ∧ (((((True → (p4 → (p2 ∧ (p4 ∨ p3)))) ∧ p4) → False) ∨ p4) ∨ p5))) ∨ (((p4 → p3) ∧ True) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178961454101652665883157625561 : (((p1 ∨ p4) ∨ (False ∧ (p3 ∨ (((False ∧ (False → p4)) ∨ p3) ∨ p4)))) ∨ ((True → ((p2 ∧ p4) ∧ p1)) → (((p5 ∨ p5) ∧ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336092964482381338640650559018 : (p1 → ((((p2 ∧ p2) → (((p5 ∨ (p2 ∧ (p3 ∨ p5))) ∨ (((p4 ∧ True) ∧ (p2 → (p1 ∧ False))) ∨ (p2 ∨ p1))) ∧ p2)) ∧ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112663443404901617005112060327 : (((((p3 → ((p1 ∨ p2) ∨ ((p4 → p4) → (True → (True ∨ p4))))) ∨ (p5 ∧ (p4 → p1))) ∨ ((False ∧ p5) ∨ False)) → p1) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309863945511055477913978959016 : (p2 ∨ ((p3 ∨ ((((p1 → (((p2 ∨ (False ∧ p4)) ∨ (p4 ∧ p5)) ∧ (p5 → p5))) → True) → p4) ∨ p4)) → (((p3 ∧ p3) ∨ p4) ∨ True))) := by
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
theorem thm_5_vars_143992654791984862758700094758 : (((True ∧ ((p4 ∨ p3) ∧ (((((p4 ∨ True) → p3) → (False ∨ p5)) → p1) → ((p1 ∨ p3) ∧ p2)))) ∨ True) ∧ ((p1 ∧ (p5 ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_302617193581478086122893963259 : (False ∨ (p2 ∨ ((((((((False ∨ p5) ∧ (p1 ∨ (p3 → (True → (p4 ∧ p4))))) ∨ False) ∨ p5) ∧ ((p5 → p2) ∧ False)) ∧ p1) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_495458958670616021845021798071 : ((((False → ((p1 → p5) ∧ p4)) → (((p5 ∧ ((((p4 ∨ p4) ∨ (p2 ∧ (False ∧ (p3 ∧ p4)))) ∧ False) ∨ p1)) ∧ p2) ∨ (p3 ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314227543804498959712146462120 : (p3 ∨ ((((p3 ∧ ((p3 → ((p4 ∨ p5) ∧ (False ∧ p4))) ∧ (((p4 ∧ p5) ∧ False) ∨ (False → False)))) ∧ p5) ∨ False) ∨ (p1 → (False ∨ True)))) := by
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
theorem thm_5_vars_317765716223313979630025895025 : (p4 ∨ ((((p1 ∧ ((False ∧ p4) → p4)) → (((p2 ∨ (p5 ∧ True)) → p2) ∧ (True ∨ p4))) → ((p1 ∨ p5) ∨ ((p3 ∧ p4) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605082763071046333381494846072 : ((((p2 → (((True → p4) → (((False ∧ p1) ∧ p5) → ((True ∧ (p3 → (p1 ∨ (True ∧ ((False → p3) ∨ p5))))) ∨ p5))) → False)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50485527493447325502298314869 : (((p3 → ((p5 ∨ p5) → (((p4 ∨ p1) ∧ ((p2 → True) → True)) → ((p1 ∨ p5) ∧ (p5 ∧ False))))) ∨ ((p1 → (p3 ∨ p5)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68910653711654400253711586952 : ((p4 → (False ∨ (((((False ∨ ((p3 ∨ (p4 ∧ True)) ∧ p3)) ∧ p5) → ((((True → p1) ∨ p4) ∨ p4) ∨ True)) → False) ∧ (p1 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117295995891719386264510152852 : ((False ∧ (((True ∧ ((p5 ∨ (False → (p4 ∨ p4))) → p2)) ∧ ((((p4 → (p1 → p5)) ∨ p5) ∧ p5) ∨ p3)) ∧ (p3 ∨ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60925560241570782113419788564 : ((False ∧ (((((p4 ∧ ((p2 ∨ p5) ∧ False)) ∧ False) ∧ True) ∨ (p3 ∧ (p3 ∨ (p5 → ((((p4 ∨ True) ∧ p5) → p5) → p4))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655641929643021846231506596552 : (((((((((False ∨ (p5 ∨ p4)) → (((p3 ∧ p4) ∨ p5) → False)) → (False ∧ False)) → p3) ∧ p3) ∧ ((p5 ∧ p3) → p5)) ∨ (True ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159687295632799028484661717374 : ((((((p1 ∨ (True ∨ p4)) ∧ True) ∨ (((p1 ∧ p1) ∧ True) ∧ (p1 ∨ p2))) ∨ (p1 → True)) ∨ p5) → (((p4 ∨ True) ∨ True) ∧ (False → p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h22
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111625028687973984134473158847 : (((((p1 ∧ (p3 ∧ (p2 ∨ (p3 ∧ (((p3 ∨ (p4 → (p2 → p4))) → (p3 ∧ False)) ∨ True))))) ∨ (p1 ∧ False)) ∨ True) ∨ False) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111118267814815906402439595793 : ((((False → ((((p2 ∧ p3) ∧ p1) → (True → p5)) ∨ p4)) → (((p4 ∨ ((p3 → (p3 → False)) ∨ False)) ∨ True) ∨ False)) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137752352852264233691716218876 : ((p2 ∨ (((p3 ∧ p5) ∧ (((True → False) ∨ ((((p5 → False) → True) → (False → True)) → (False ∨ p5))) ∨ True)) ∨ p3)) ∨ ((False ∧ p3) → p2)) := by
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
theorem thm_5_vars_149704146200038717125234072194 : ((p5 ∧ ((p3 ∧ p5) → ((((False ∧ ((p2 ∧ p3) ∨ p1)) ∧ True) → ((True → p3) ∧ (p3 ∨ p5))) → p2))) ∨ (((p3 ∧ p5) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184584651172462240270561921192 : (((False ∨ (((p4 → (p3 → p1)) ∧ p2) ∧ p2)) → (p5 ∧ p1)) ∨ ((((p5 → (p1 ∨ p5)) ∧ p1) → ((p1 ∧ True) ∨ (p4 ∨ p2))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199964137010221410744130101818 : (((p1 → (p1 → (p4 ∨ p3))) ∨ (p4 ∨ False)) → (p5 → (((p4 ∧ (p3 ∨ ((p1 ∧ p5) → (p4 → p4)))) → (p2 → (p2 ∧ p3))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55702650064935979777375785767 : ((((p5 ∧ (p4 ∨ p5)) ∨ p3) ∧ ((((p2 ∧ p3) → (p4 ∧ ((False → p3) ∨ p4))) ∧ (p3 → p5)) ∧ ((False ∨ p3) ∧ (True ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158939977366933294010659209201 : ((p2 ∨ ((((True → p4) ∨ p1) ∧ (p5 ∧ ((p4 ∨ (p3 ∧ (p5 ∨ p4))) → p5))) ∨ (p2 ∧ True))) ∨ (p4 ∨ (True ∨ ((p5 ∨ True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313305889521531479880948749542 : (p3 ∨ ((False ∨ ((p2 ∧ False) ∧ ((p1 ∧ (p2 ∨ (((True ∧ ((p2 → p3) → (False ∧ (p5 ∨ p3)))) → (p4 ∨ False)) ∨ True))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310854719394921514319272743068 : (p2 ∨ (((p5 ∧ False) → False) → (((p4 ∨ (p3 ∨ ((p4 ∨ p5) ∧ p2))) ∨ (p1 ∨ (p1 ∨ ((((p2 → p3) → p4) ∨ p2) → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791370828250677293779035828442 : (((True → (((p4 → ((p5 → ((p4 ∧ p5) → p1)) ∧ (p2 ∨ ((p2 ∧ (p4 ∧ p5)) → (p3 ∨ p3))))) → ((p3 → p4) ∨ p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678562633208652331189265314995 : ((((((p2 ∨ p5) ∨ p2) → ((p5 ∧ (p4 → p5)) ∨ (False ∧ (p4 → ((p3 ∧ p5) ∧ (p2 ∧ p4)))))) ∨ (p3 ∨ (True ∨ (p4 ∧ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38117138462665877684092009126 : ((((((p2 ∧ (p5 ∨ p5)) ∨ (p4 → (((((p4 ∧ p1) → p1) ∧ p3) → True) ∨ p1))) ∧ (p5 ∧ p1)) ∧ (p5 → (p5 ∨ False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134218579164522805761718877587 : (((((p3 ∧ (p4 → p5)) ∨ (p4 ∨ True)) ∧ ((((p1 → (False → ((p1 → True) ∨ False))) ∧ p4) ∨ False) → p3)) ∨ True) ∨ (p3 ∧ (False ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676521843827339459496217019503 : ((((False ∧ ((((p1 → (((((False ∧ p2) ∧ p1) → (p5 ∧ p3)) ∨ p5) → p5)) ∧ p4) ∨ p4) ∧ p5)) ∧ (((p3 ∧ True) → p3) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252666609538108309909318184206 : ((p5 → p4) ∨ ((p3 → p5) → ((((False ∧ p5) ∧ p3) ∧ ((p2 → ((True ∨ p5) → (p4 ∧ (p5 ∧ p5)))) ∨ False)) ∨ (p4 → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656876447787043392023561525212 : (((((p1 → ((p1 → p4) ∧ p3)) ∧ (((p1 → ((p4 → (p2 ∧ (p1 → ((False ∧ p1) ∨ p5)))) ∨ p3)) ∨ p5) ∧ p3)) ∨ (p3 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313052302778051852576562458023 : (p3 ∨ ((((p4 ∧ (p4 → (p1 ∨ True))) → ((False → (True ∨ ((p4 ∧ (p4 → p4)) ∧ (p1 ∨ ((p4 ∧ p5) ∧ p1))))) ∧ p5)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2450443613268559800236006921 : ((((p5 ∨ (p3 ∧ ((p1 ∨ p2) → p5))) ∧ False) ∨ True) ∨ ((False ∧ (((p2 ∧ False) ∨ p4) ∨ (p1 ∧ p3))) ∧ ((p5 ∨ True) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587008836779842063349838604501 : (((((p5 ∨ (((((p4 ∨ True) ∧ ((p3 → (p3 ∨ ((p5 ∨ p2) → False))) → p5)) → p4) ∧ (p5 → (False ∧ False))) ∧ p3)) ∧ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310027051028927492159036005754 : (p2 ∨ (((False ∨ (((p2 ∨ (p1 ∨ p4)) ∨ p3) → (p1 ∧ (True ∨ p1)))) → (True ∧ p1)) ∨ (True ∨ ((True ∨ p3) ∧ (p5 ∨ (p1 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217158906259702301599747732021 : ((((True ∧ p3) → p2) ∨ p2) → ((((p4 → p5) ∧ (False ∨ ((p5 → p1) → p4))) ∨ (True ∨ False)) ∨ ((True → (p1 ∧ True)) ∧ (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164930464493140178223988328481 : ((((((p1 ∨ p3) ∨ False) → (p5 ∧ (p1 → ((p5 ∧ p3) → (p3 ∧ p2))))) ∨ p3) → False) ∨ (((p1 ∧ p1) ∨ p2) ∨ ((True ∧ False) → False))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111800771834558113244103612535 : (((((((True → False) ∧ p2) ∧ (p5 ∨ (((False → p5) ∨ (p2 ∧ (p1 → (p4 → p5)))) ∧ p2))) ∨ p5) → (p1 ∨ p5)) ∨ True) ∨ (True ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328317912957548285321513162777 : (True → ((((p4 ∨ ((True ∧ p4) ∨ ((p5 ∧ p2) ∨ p5))) → (((p5 ∨ p5) → (p2 ∨ p2)) → True)) ∧ p3) → (((p4 → False) ∧ False) ∨ p3))) := by
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
theorem thm_5_vars_611598712071577988268231967687 : (((((p1 ∨ ((((True ∨ (p1 ∧ True)) → (True → (p3 → ((p2 → True) ∧ p3)))) ∨ ((p3 ∨ (p5 ∨ p2)) ∧ False)) → True)) → False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760105971844188156878001517 : (((p2 → (p4 ∨ p3)) → (((((False → p3) → ((p2 → p2) ∨ p3)) ∧ p4) → p3) ∨ ((p2 → (p1 ∧ (p4 → p1))) → True))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158366394519682148258344544065 : (((p3 ∨ True) ∧ (((p3 ∨ (p1 ∧ p2)) → ((p5 → (p5 ∨ (True ∨ True))) → p1)) → (p5 ∧ p2))) ∨ (p2 → (p3 → (False → (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674955633326643370660917564501 : ((((((True ∧ (((False ∨ p4) → ((p3 → p2) ∨ p1)) → True)) → (False ∨ (p3 → (p4 ∨ True)))) ∧ True) ∧ (p1 ∨ ((False ∨ False) ∨ True))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204688308859745179728457134083 : (((p2 ∨ ((p1 ∧ p5) ∨ p1)) ∨ False) ∨ ((((p3 ∨ ((False ∨ p5) → p2)) → (p2 ∧ ((((False → False) → p3) → True) → p5))) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340762202488158245795645157810 : (p2 → (((p3 ∨ ((p3 ∧ ((p1 → False) ∧ ((False ∨ False) → (p1 ∨ (((False → p3) ∧ (p2 ∧ p5)) ∧ p2))))) → (p4 ∨ p4))) ∨ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49328311520632105091631196388 : (((p4 ∨ (p5 ∨ ((False ∨ True) ∧ ((((((p1 → (p3 ∧ p4)) ∧ True) ∨ p1) → (p3 ∧ p2)) ∨ p4) ∨ p3)))) ∨ (p3 ∧ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135285782590771199160908633288 : (((p3 → (((((((p3 ∨ ((False ∨ True) → p3)) ∨ (p1 → p2)) ∧ False) → True) ∧ p1) ∨ p4) ∧ p2)) → (p4 ∧ False)) ∨ ((False → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164715360886458248687299934184 : ((((((p2 ∧ (((p3 ∨ (False ∧ False)) ∧ p4) → p5)) ∨ (True ∧ p1)) ∨ p4) → p3) ∨ True) ∨ ((False ∧ ((p4 → (p4 ∨ False)) ∨ p4)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711727525795689964409389996917 : (((((((p5 → False) → p2) ∧ True) ∧ p4) ∨ ((p4 → (p2 → (True ∧ ((((p3 ∨ (p3 ∧ p4)) → (p1 → p5)) ∧ p1) → p4)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63085699736439888225755326142 : ((p5 ∧ ((((p2 ∨ p5) ∧ ((p4 → ((((p3 → p4) ∨ False) ∧ True) ∨ (p5 → True))) → (p3 ∧ p2))) → (False ∨ (False ∧ p4))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245815860812769951908275101942 : ((p3 ∧ p3) ∨ (True → (((p2 → (p4 → (p3 ∨ (((p1 ∧ (False ∧ (p5 ∧ (p2 ∨ False)))) ∧ p1) ∨ p2)))) ∨ True) ∨ ((True ∨ p4) → p1)))) := by
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
theorem thm_5_vars_661735965041346416994969633164 : (((((p3 ∧ ((p3 → (p3 ∧ ((p3 ∨ ((p1 ∧ (p1 ∧ p1)) → False)) ∧ p1))) ∧ p3)) ∧ ((True → (p5 ∨ p3)) ∧ p3)) → (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174104723795615929775939362933 : ((((p4 ∧ p5) ∨ (((p1 → p2) ∧ (p3 ∧ (p5 ∧ p4))) → p2)) ∧ (True → p1)) → (p1 ∨ ((False ∨ (p5 ∧ True)) → ((True ∨ p3) ∧ False)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51075217866711050046148483705 : (((p3 → (((p5 → (p3 → (p2 ∨ p2))) → (True ∧ False)) ∧ ((p4 → p1) ∧ (False ∨ p2)))) ∧ (((p1 ∨ False) → (p5 ∧ p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306659448207409176877799705271 : (p1 ∨ (True ∧ (((((p1 → p3) → (p2 ∧ p3)) ∨ p2) → p2) → ((((p5 → p3) → ((p3 → False) ∧ p2)) ∧ False) ∨ (p5 → (True ∨ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



