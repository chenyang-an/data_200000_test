variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731455697184923746878438282666 : ((((True → (False ∨ p1)) → (p4 ∨ ((p4 ∨ ((p3 ∧ p5) ∨ p2)) ∨ (((True → (p1 → ((p1 ∧ p5) → False))) ∧ (False ∧ p5)) → p4)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158250781267711517870034815048 : ((((p1 → p4) ∨ p1) ∨ (((p5 ∧ p4) → (((p2 ∧ False) → p2) → ((False ∧ True) → p2))) → p1)) ∨ ((p4 → p1) → (True ∧ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338428056457474926880409212780 : (p1 → ((p4 ∨ (True ∨ (p3 ∧ False))) → ((((((p2 ∨ False) ∧ p5) → (((p4 ∧ (p2 → False)) ∨ (p1 ∧ False)) ∨ p5)) → False) → False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∨ False) ∧ p5) → (((p4 ∧ (p2 → False)) ∨ (p1 ∧ False)) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h5
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (((p2 ∨ False) ∧ p5) → (((p4 ∧ (p2 → False)) ∨ (p1 ∧ False)) ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h21 := h14 h15
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199667301492278381408147799526 : ((((False ∧ p4) ∨ (p5 → (False → True))) → False) → ((((((p3 → p2) ∨ False) ∧ (p1 ∨ ((True → p1) ∨ p2))) ∧ (True ∧ False)) ∨ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p4) ∨ (p5 → (False → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61809140232251308889538414386 : ((p2 ∧ ((((p1 ∧ ((p3 → p4) → False)) ∨ ((p5 ∨ (p5 ∧ ((p2 ∧ p1) → True))) ∨ (True ∧ p3))) ∧ (p4 ∨ (p4 ∨ True))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735262907107697903023325353271 : ((((p3 ∨ p5) ∧ (p4 ∧ (((((p4 → (False ∨ (p4 ∨ True))) ∨ p5) ∧ p4) ∨ ((((p2 → p4) → p1) ∨ (True ∧ p5)) ∨ p5)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207075862804976025839005548266 : (((p3 ∧ (p4 → (p5 ∧ True))) ∧ p2) → (((p3 ∨ (p2 ∨ ((p1 → (True ∨ p3)) → p2))) → ((p5 → (p1 → p4)) ∨ p5)) ∨ (p2 ∧ p3))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146982059375803256276356083143 : (((((p2 → (p2 ∨ p4)) ∨ (False ∧ ((((True ∨ p4) ∨ ((p5 ∧ p3) ∧ True)) ∧ p5) ∧ p2))) → False) ∧ False) ∨ ((True ∧ False) → (False ∧ p2))) := by
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
theorem thm_5_vars_199288900402236095230636001879 : ((((False → ((p4 ∧ p2) ∧ p4)) ∧ p2) ∨ p3) → (((p3 → (False ∨ p1)) ∨ (((((p5 ∨ False) → True) → p1) → True) ∨ p2)) ∧ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520192312755610238737217774606 : ((((p3 ∨ p2) → (p5 ∨ ((p2 ∨ ((p5 ∨ p5) ∨ True)) ∨ ((((True → (p1 → p4)) ∧ p1) ∧ p5) ∨ ((p4 ∧ p2) → (p5 → p4)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56847707135264312641880181207 : (((True ∧ (p1 ∨ True)) ∧ ((p4 ∨ (((p3 ∧ ((False → p3) ∧ (p1 → False))) ∨ (p1 ∧ (p4 ∨ False))) ∨ p3)) ∧ (p5 ∨ (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619781607007104338429349312827 : (((((p1 ∨ p1) ∧ (p5 → (((((p3 ∧ p3) ∨ p4) ∨ (((p3 ∨ True) ∧ ((p5 ∨ True) → True)) → p3)) ∨ (p5 → p3)) → p3))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135918143745161787858518378487 : ((((p2 ∧ True) → (((p2 ∨ (p3 ∧ p1)) ∨ False) ∨ (p2 → p3))) → (((p4 ∧ (False ∨ (p4 ∨ p2))) ∨ True) ∧ p5)) ∨ (p1 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608103769103732399691645791276 : (((((((p1 ∨ (p5 ∨ (((p5 ∨ ((p4 → p4) → (p5 ∨ p1))) ∧ (p4 ∨ False)) ∧ (p3 ∧ False)))) ∨ (p1 ∧ p4)) ∧ p1) ∨ p3) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78620616949116900919544693238 : (((((((p5 ∧ p2) ∧ (p4 ∨ (True ∧ p3))) ∨ False) → ((p1 ∧ False) ∨ (p2 ∨ (p3 ∨ (p2 → p3))))) → (p1 ∧ p2)) ∧ (True ∨ p3)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((p5 ∧ p2) ∧ (p4 ∨ (True ∧ p3))) ∨ False) → ((p1 ∧ False) ∨ (p2 ∨ (p3 ∨ (p2 → p3))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
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
        cases h9
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h5
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : ((((p5 ∧ p2) ∧ (p4 ∨ (True ∧ p3))) ∨ False) → ((p1 ∧ False) ∨ (p2 ∨ (p3 ∨ (p2 → p3))))) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h31 =>
        -- False on the left can always be used.
        apply False.elim h31
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h20
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111942663639197100287669695268 : (((((p4 ∨ (p4 ∨ True)) → (False → ((p2 ∧ p5) → p4))) → (((p3 ∨ (True → p5)) ∧ (True ∧ p3)) ∧ (False → p4))) ∨ True) ∨ (p5 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165751424951089712448224980938 : (((p1 ∧ (p2 → (p5 ∨ p5))) ∨ (p4 ∨ ((p1 ∨ p1) ∨ (p2 ∧ ((p5 ∧ p5) ∨ p5))))) ∨ (p3 ∨ ((p1 ∨ (p5 ∧ p2)) → (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157963228747157902023037248864 : (((((p1 → p4) ∨ (False ∨ p1)) → (p5 ∨ False)) ∨ (((p2 ∧ True) → p1) → (p5 ∨ (True ∧ p1)))) ∨ (((p2 ∧ False) ∨ True) ∧ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46809704630193860410697824168 : ((((((p4 ∨ ((p4 ∧ (True ∨ ((p4 → ((p1 ∧ (p3 → p5)) ∧ p5)) ∧ p1))) → True)) → (False ∧ p4)) ∨ p5) ∧ p3) ∨ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134087556665378462347748398894 : (((((p2 → (p5 ∨ p5)) → ((p4 → (p4 ∨ p1)) → (p5 ∧ (False ∨ (p4 → (p1 ∧ (p1 → False))))))) → p3) ∨ False) ∨ (True → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50635870721337458374619973165 : ((((p1 → (((False ∨ p3) → (False ∨ p2)) ∧ ((p1 ∧ p5) ∧ p4))) ∧ ((p5 → (True ∨ p1)) ∨ p2)) → (p4 → ((p3 → p4) → p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230720785095357263654189942431 : (((p5 → True) ∧ p3) → (((p4 ∨ (False ∨ (p1 ∧ (p4 ∧ (True ∨ (((((p4 ∨ p3) ∧ (p3 ∨ p5)) ∨ p1) → p5) → p3)))))) ∨ p5) ∨ p3)) := by
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
theorem thm_5_vars_135159167843923846985140405054 : (((p5 → ((p4 ∨ (p4 → ((p1 → (((p5 ∨ p3) ∧ (p4 → False)) → p5)) ∨ False))) → (p5 ∧ p3))) ∨ (p2 ∨ p1)) ∨ ((False ∧ p3) → False)) := by
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
theorem thm_5_vars_671196028507431451177998196583 : ((((p3 ∨ (((p4 ∧ p3) ∧ (((p1 → p4) ∧ (False ∨ (p5 ∧ (p2 ∧ True)))) ∧ p1)) ∨ (p5 → (p5 ∧ p4)))) ∨ ((True ∨ False) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51873426571583389456046674186 : ((((False ∧ (p5 → (p2 ∨ (((p2 ∨ p4) → ((True ∨ p4) → False)) ∨ True)))) ∨ True) ∨ ((p2 ∧ (p4 → (p1 ∨ p5))) → (p5 ∧ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188416537829272093135288945954 : (((((p4 ∧ p2) → (p1 ∧ p3)) → (p3 ∧ p4)) → True) ∧ ((((p3 ∧ p5) → ((p5 → p2) ∧ p3)) → True) → (p1 → ((p5 ∨ p1) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14694066562596204505071300307 : ((((((((p3 ∧ (p4 → p2)) → (((p2 ∧ True) ∧ p5) → False)) → (p4 → (p2 ∧ p1))) ∨ p3) ∨ p1) ∨ (p3 ∧ True)) ∨ (p4 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_37886280192010585873588026543 : (((((p5 ∨ (((False → p4) ∧ (((p3 ∧ True) → ((p1 ∨ p1) ∨ True)) ∨ ((True → True) → p1))) ∨ p2)) ∨ p1) ∧ (p2 ∧ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64214484465571102585068751815 : ((False ∨ (p3 ∧ (True ∧ (p1 → ((((True → ((p2 ∧ (p5 ∨ p3)) ∧ (((p3 → True) → False) ∧ False))) ∧ (p1 → p5)) ∧ p5) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310637010877085187038936370724 : (p2 ∨ ((p4 ∧ (p1 → (False ∧ p2))) ∨ (p4 ∨ ((True ∨ ((p4 ∨ True) ∨ ((False → ((p5 ∧ p3) ∧ (False ∧ p1))) → True))) ∨ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_624426689454491957311714829729 : ((((p3 ∨ (p2 ∨ (((p1 → (p5 ∧ (False ∧ ((p5 ∨ ((True ∧ False) ∨ (p1 ∨ p2))) ∨ False)))) ∧ p2) ∨ (p4 ∨ (p3 → True))))) ∨ p1) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_804745084158934543338407467788 : (((p3 → ((p4 ∧ (p4 ∨ False)) ∨ (p3 → ((p1 ∧ (p2 ∨ p3)) ∨ (((True ∨ p1) ∧ False) → ((False → ((p1 ∨ p4) → p5)) → p4)))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326343071315415421256987250913 : (p5 ∨ (p5 → (((p4 → False) ∨ (((p1 ∨ p2) ∧ p1) → (((((p3 → p4) ∧ (p2 → ((p4 → False) → p2))) → False) ∨ False) ∨ True))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204169991363936718101859840219 : ((((p1 ∧ (p4 → True)) ∨ p5) ∧ p1) ∨ (((p5 ∧ p4) ∨ ((p3 → p5) → (p3 ∨ p2))) ∨ ((False → (False → (True ∨ p5))) ∨ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64593903412974381513341256488 : ((p1 ∨ ((p4 ∧ p3) ∨ ((p3 ∨ (p1 ∧ (False → (p3 → p2)))) ∨ ((p4 ∧ True) ∨ (False → ((p5 → True) ∧ (p2 ∧ (p3 ∨ True)))))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197389350488456396682928272722 : (((p3 ∨ (False → (False → (True ∨ True)))) → p3) ∨ ((p4 → p4) ∨ (((False ∧ (((p1 ∧ p5) ∨ p1) ∧ (False ∧ False))) ∨ (p5 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262275589036819411449378380181 : (True ∧ (((((p2 ∧ ((p5 → (p4 → ((p5 ∨ (True → p2)) ∨ (True → p1)))) ∨ False)) → p4) ∧ p1) → (((p3 ∨ False) → p5) ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64293269941030668755753971743 : ((False ∨ (p3 → (False ∧ (p1 ∧ (p2 → (False ∧ (((p4 ∧ ((p4 ∨ p4) ∨ False)) ∧ (p3 ∧ (True ∨ (p4 → (p1 ∨ p2))))) ∨ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114707870583253965639545477272 : ((((p1 ∨ (((p1 ∨ p5) → (p4 ∧ p1)) → ((p1 ∧ p5) ∧ (False → p5)))) ∨ p5) → (((p5 → (p5 ∧ p2)) → p2) ∧ False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151932972920649847629371426895 : (((((p1 ∨ p5) ∧ (p3 ∨ True)) → (((p1 ∧ False) ∧ p3) ∧ p1)) ∧ (((p4 ∨ p1) ∨ (p5 → p1)) → p5)) → (p1 → ((p2 → p1) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∨ p5) ∧ (p3 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638457377007950097068977281153 : (((((((p5 → p1) ∨ (p5 ∧ p3)) ∧ p4) ∨ ((p5 ∧ (False ∧ (False → ((p4 ∨ p5) ∧ (p1 → (False ∧ (p1 → p5))))))) → False)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148129487355291965761605706623 : ((((p2 → False) ∧ (((p1 ∧ ((False ∨ ((True → p1) ∨ p2)) → p1)) ∨ True) ∧ (p1 ∨ p3))) → (p5 → p3)) ∨ ((p5 ∨ True) ∧ (True ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65288173343729915820999407675 : ((p3 ∨ (((p4 ∧ ((((p2 ∨ p5) ∧ ((p4 ∨ (p4 ∧ p4)) ∧ False)) ∧ ((p5 → (p3 ∨ p1)) → p4)) → True)) → p2) ∨ (True ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_164786191226476214542812631444 : (((((False ∧ (p3 ∨ p4)) ∧ p1) ∧ (True → ((((True → p5) ∧ p3) ∨ p5) ∧ p5))) ∨ p1) ∨ (p2 ∨ ((p2 → (p1 → (False → p3))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149783664650948535361231337009 : ((False ∨ (((p4 ∧ p5) ∨ (((((p1 ∧ p2) ∨ p2) ∧ p3) → (p3 ∧ p4)) → p1)) ∨ (True ∨ (p2 ∧ False)))) ∨ (p2 ∨ ((p2 ∨ p1) ∨ False))) := by
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
theorem thm_5_vars_204125295552738717557413672608 : ((((False ∧ (p3 → True)) ∧ p3) ∧ p1) ∨ ((True ∧ (((True ∨ (p5 ∧ p3)) ∧ (False ∧ p4)) ∨ ((p2 → p3) → (p5 → (p3 → True))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301517253944643138006827830150 : (False ∨ (((True ∧ True) ∧ p2) ∨ ((True → (False ∨ ((p1 → ((p4 ∨ p4) ∨ p2)) → ((p4 ∧ (p2 ∧ p1)) ∨ (p3 ∨ True))))) ∨ (p4 ∧ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230487257142906464282214113949 : (((True → False) ∧ True) → ((True ∧ (p2 ∨ (((p3 ∨ p5) ∨ (((p5 ∧ (True → False)) ∧ (p2 → False)) ∧ p1)) → False))) → ((False ∧ False) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135809402143538027554574770110 : (((p3 → ((((((p5 → p1) ∧ p3) ∧ (p1 ∨ p5)) ∧ p4) ∧ p1) ∧ p1)) → (p5 ∨ ((p1 ∨ (p5 → p4)) ∨ True))) ∨ (False → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155781922793872133837819089328 : (((True → False) → ((p1 ∨ ((((p2 ∧ (p2 → p1)) ∨ p1) ∧ p2) ∨ (True → (False → True)))) ∨ p1)) ∧ (((p3 ∨ False) → p2) ∨ (p1 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_298787685259798578331042271430 : (False ∨ (((((((p2 → (((p1 ∨ True) ∨ p5) ∨ p5)) → p1) → p5) → (p3 → (((False ∧ p5) ∨ p5) ∧ p1))) → p1) ∨ (p5 → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140519668445184515846415266370 : (((False ∨ ((p2 ∧ p5) ∧ (p5 ∧ (p3 ∧ ((p5 → (p5 ∧ (False ∧ p2))) ∧ p5))))) ∧ (False → ((p3 ∨ p1) ∨ p2))) → (p1 ∧ (p4 ∧ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h25.left
    let h29 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h34 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h33
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h35 := h32 h34
    -- We need to get the right conjuct of h35 based on <expert-advice>.
    let h36 := h35.right
    -- We need to get the left conjuct of h36 based on <expert-advice>.
    let h37 := h36.left
    -- False on the left can always be used.
    apply False.elim h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- False on the left can always be used.
    apply False.elim h40
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h42.left
    let h45 := h42.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h43.left
    let h47 := h43.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h50 := h49.left
    let h51 := h49.right
    -- One of the premise coincides with the conclusion.
    exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158118904727896096216815581267 : (((p1 ∨ (p3 ∨ (p5 ∧ p5))) ∧ ((p2 ∨ ((p4 → True) ∧ ((True → (False ∨ p3)) ∨ False))) → p3)) ∨ ((True ∨ (p1 ∧ (True ∨ p5))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52411881898409566586205609604 : ((((p2 ∨ (p5 → p3)) ∨ ((p4 ∨ (p5 → p1)) → ((p3 → p1) ∨ True))) ∧ ((p2 → (False ∧ p3)) → (((p3 ∨ False) ∧ p2) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178868983200339852464569759766 : (((p5 → (p5 → p4)) → ((((p4 ∧ (p3 → p2)) ∧ p2) ∨ True) ∨ False)) ∨ (((p1 ∧ (p1 ∨ p3)) ∨ ((p3 ∨ p5) ∨ (p4 → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345085799227028131573901695221 : (p3 → ((((True ∧ p2) → (((p4 ∨ (p1 ∧ p4)) → (p1 ∨ p5)) → (p1 ∨ p5))) ∨ ((p4 ∧ (p4 → p3)) → (True → (False → p1)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54023435607699929805228556379 : ((((((p4 ∨ p2) → p5) ∧ (p1 ∧ p4)) ∧ (True ∧ p4)) → ((((((p4 → False) ∨ p3) ∧ ((False ∨ p1) ∨ p3)) ∨ p1) ∧ p4) ∧ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h8 := h3.left
  let h9 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h11.left
  let h17 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h19.left
  let h25 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54313070967456716998305291002 : ((((False → p4) → ((p2 → p1) → (False ∧ p1))) ∧ (((((p1 ∧ (p1 → (False ∧ p4))) ∨ ((False → p1) → p4)) ∨ p1) → p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612158328101636342801343208052 : ((((((((p3 ∨ (p5 ∨ p5)) → ((p1 → p5) → p4)) → p5) ∧ ((p1 → p1) ∨ (p1 ∧ ((p1 → p3) → p3)))) ∧ (p2 ∨ p1)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_50494642942023822036981176233 : (((p5 → (p1 ∧ (p1 ∨ (((p3 ∨ (((True → (False ∧ p1)) ∨ p5) ∨ (p5 ∨ p5))) → False) ∧ True)))) ∨ (True ∨ ((False ∧ True) ∧ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316679424450417221926818133937 : (p3 ∨ (p5 ∨ ((((((p2 ∧ True) ∧ (False ∨ p3)) ∨ (False → (((True ∨ p2) → p3) → (False → p2)))) ∨ (p1 → True)) ∨ p1) ∧ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49662006829215473247345493024 : (((((p1 ∨ p4) → True) ∨ (p1 ∨ (((p4 → (p2 ∧ p1)) ∧ p2) ∧ (((p1 ∨ (p2 ∧ p5)) ∨ p4) ∧ True)))) → (p2 ∨ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136640450732896587488975238338 : ((((p2 ∧ False) → True) → ((p4 ∨ ((p5 ∧ p3) → ((False → p3) → p2))) ∨ (((p1 → p4) ∧ (False ∧ False)) ∨ p4))) ∨ ((False ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56433084184734216327243073768 : ((((p2 → False) ∧ (True ∧ p4)) → ((True ∧ ((False ∨ ((p2 ∧ (p2 → (p3 → p1))) → (((True → p1) ∧ p5) ∨ False))) ∧ p1)) ∨ p4)) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44510027109822822964921480521 : (((((True ∧ ((False → ((False ∧ p4) → True)) ∧ p3)) ∨ p3) ∨ ((p3 ∨ ((p2 ∨ (p4 ∨ ((p2 → p2) ∨ True))) → p3)) → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39575156530214980139408814395 : (((p1 ∨ ((p4 ∨ True) ∧ (((((True → ((p1 ∨ p3) ∨ p1)) ∧ p4) ∧ p2) → (p4 ∨ p1)) → ((p5 ∧ p2) ∧ (p4 → p1))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137847606104158705263183490059 : ((p3 ∨ (((p3 → False) ∨ False) ∧ ((((True → p5) → False) ∨ (p3 → (False → p3))) → ((False ∧ (False ∧ p5)) ∧ p3)))) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753027733637666524536610280197 : (((False ∧ (((p1 ∧ p3) ∧ (p3 ∧ (((False → True) ∨ (False ∨ (True ∨ ((p5 → True) ∨ p5)))) ∨ ((p1 → (p4 → False)) → p2)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147656125902447396385331221809 : ((((p2 ∨ (p1 ∨ ((False → False) ∨ (p3 ∨ (False → ((False → True) ∧ (p2 ∧ p1))))))) ∧ (p4 ∨ True)) → p1) ∨ (False ∨ (p1 → (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37091374709118740551796407124 : (((((p2 ∧ (True ∧ ((p1 → ((p4 ∨ p3) ∨ (p3 ∨ p5))) ∧ ((True → p1) ∧ (True ∨ ((False ∧ p5) ∧ False)))))) ∨ False) ∧ True) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2953681865833252768318916735 : (((p1 → p5) → p2) ∨ ((p5 ∧ ((p5 → (((p5 ∨ p4) → (p3 ∨ p4)) ∨ (p5 ∧ p1))) ∧ p1)) ∨ (((True ∨ False) ∨ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_133924138508678592923206729911 : (((p5 ∨ ((p4 ∨ (((p3 ∧ (((p4 ∧ p4) → ((p3 ∧ (p3 ∧ p4)) ∨ p2)) → p1)) → False) ∨ True)) ∨ False)) ∧ True) ∨ (True ∧ (False ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_341067371010376552372690080578 : (p2 → ((p4 ∨ (p2 ∧ (p3 ∧ ((p4 ∨ ((p3 → ((((False ∧ (p3 ∨ (p3 → p3))) ∧ False) ∨ True) ∨ p1)) ∨ p1)) ∨ (False → p3))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136642555154041946758915803084 : ((((p5 ∧ p3) → p5) → (((p5 ∧ (((False → p5) ∨ (p2 ∧ (p4 → False))) → (p4 → True))) ∨ p4) ∧ (p5 ∨ p1))) ∨ (True ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160252724207817037806254999971 : ((((p5 → p3) → (True ∧ ((True → ((((False ∨ False) ∨ p2) → p3) ∨ p1)) → p2))) ∨ (p4 → p5)) → (True ∧ (((p3 ∧ p2) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_47699620480302228000769753085 : ((((p2 → ((((p1 ∧ p1) ∧ (False ∧ (p1 ∧ ((p2 ∨ p5) → p1)))) ∨ ((p3 ∨ (False → True)) ∨ p5)) → True)) ∧ p1) → (p3 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184254192955228273708680635401 : ((((p4 → ((p1 ∨ (p5 → False)) ∨ (p3 ∨ p5))) → p2) → False) ∨ (True ∧ (((p2 → (False → (True ∧ (p5 ∨ (p2 ∧ False))))) ∧ p4) → True))) := by
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
theorem thm_5_vars_262437847064953579958043958811 : (True ∧ ((p5 ∧ (((False ∧ p5) ∨ (((True → ((p2 ∧ ((p4 ∧ p5) → True)) ∨ p3)) ∨ False) → (((True ∧ p3) ∧ False) ∧ p1))) ∧ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149352036271893555846390971732 : (((p4 ∨ False) → ((((p2 ∧ (False ∨ p1)) ∨ (p5 → (p2 → (p1 → ((False ∧ True) ∧ p1))))) ∨ p5) ∧ p5)) ∨ ((True ∨ (p2 ∨ p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219089078991978053832259040174 : ((True ∨ ((True ∨ False) ∧ p4)) → ((p3 ∨ (p2 ∧ (p4 ∨ (False → ((p1 ∨ (False ∧ ((False ∧ ((p1 → p4) ∨ p1)) ∨ p1))) ∨ True))))) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316694800513971794498992338879 : (p3 ∨ (p5 ∨ ((p3 ∧ (p3 ∧ ((p4 → (p4 → True)) ∨ p2))) ∨ (p5 → ((((((p4 → True) → p3) ∧ (p1 → p2)) ∧ p2) ∧ p5) → p3))))) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148765171319873928527925676351 : ((((False ∧ (p5 ∧ (p5 ∧ False))) ∧ p3) ∨ ((False ∧ (False ∨ ((p5 ∧ p3) → p3))) ∨ (False ∨ (p5 ∨ True)))) ∨ (p1 ∨ (p3 → (True → p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157827535790613371496376129201 : (((True ∧ (True ∧ ((((p4 ∨ p2) → p4) → (p4 ∨ p2)) ∧ p5))) → ((p2 ∧ (p4 ∨ p5)) ∧ p3)) ∨ (p4 ∨ (p1 → (True ∧ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244417644463100654545739714762 : ((False ∧ p1) ∨ (p4 ∨ ((p4 ∧ ((p1 ∨ True) → p3)) → ((False ∨ ((p3 ∨ ((True ∨ p1) ∨ (True ∨ p5))) → (p3 ∨ (p1 ∧ False)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249130443406247726958447255765 : ((p4 ∨ p2) ∨ ((False ∨ (p4 ∧ ((p3 ∨ p2) → (True → (p2 ∨ (p5 ∧ p4)))))) ∨ ((((p2 ∧ ((p2 ∧ True) ∧ p1)) ∨ False) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172727305947556398720561638976 : (((p1 → False) ∨ (p2 → (p1 ∨ ((False → (((p1 → p1) ∨ False) ∧ p5)) → p3)))) ∨ ((p5 ∨ ((p2 ∧ p2) ∧ (False ∧ (p2 → p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598439766927017143143138209086 : ((((((True → p5) ∧ p1) → ((p2 → ((p4 ∨ p5) → (((p4 ∨ p5) → p3) ∨ p3))) ∨ (((p3 → p4) → (p4 → False)) ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53518403304671622530522760844 : (((False → (p5 ∨ (((True ∨ p2) → (p4 → p2)) ∨ (p4 ∧ False)))) → ((((True ∨ False) → p2) ∧ (p5 ∧ p5)) ∨ (True ∧ (p5 → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51346680774187579785005795228 : (((((((p2 ∨ (p2 → ((False → p4) ∧ p5))) ∨ ((p2 → p4) → p1)) → False) ∧ p5) ∧ p1) → ((p5 ∧ p1) ∧ ((p3 ∨ p4) ∧ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : ((p2 ∨ (p2 → ((False → p4) ∧ p5))) ∨ ((p2 → p4) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h14
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- One of the premise coincides with the conclusion.
  exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175213113090848060494974631210 : ((False ∨ (p4 ∨ (((True ∧ (p2 ∧ p2)) ∨ (True ∧ True)) ∨ ((p2 ∨ p5) ∨ p2)))) → (p4 ∨ (True → ((True ∧ p3) ∨ (p3 → (p3 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h28
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- Implications on the right can always be decomposed.
            intro h30
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h33
          -- Implications on the right can always be decomposed.
          intro h34
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165114562642274153531844056848 : (((p3 → ((p1 ∨ (p2 ∧ p3)) → (p3 → ((p2 → (p1 ∨ p3)) → (p5 → p3))))) → False) ∨ (True ∨ (p2 ∨ ((p3 → p3) → (p1 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117399326497827820706648082758 : ((p1 ∧ ((p5 ∧ ((((True → p1) ∨ True) → (p3 ∧ ((p5 → False) ∧ (((p3 ∨ p5) ∧ (False → p4)) → False)))) ∨ p2)) ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686393284410147204947022094079 : (((((((p1 ∨ p2) ∧ p3) ∨ True) ∨ (((False → p3) → ((p2 ∧ p4) ∨ (p1 → p4))) → True)) → ((p1 → ((p3 ∧ True) ∨ p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180473065780626917124265331393 : (((p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) → (True ∧ False)) → (True → ((((p4 ∨ (p5 → False)) ∨ p5) → False) ∧ (p5 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : (p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h6
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : (p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h12
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : (p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h18
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h23 : (p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h26 := h1 h23
  -- We need to get the right conjuct of h26 based on <expert-advice>.
  let h27 := h26.right
  -- False on the left can always be used.
  apply False.elim h27
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h28 : (p3 → ((((True → False) ∨ (p1 ∧ False)) ∨ False) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h31 := h1 h28
  -- We need to get the right conjuct of h31 based on <expert-advice>.
  let h32 := h31.right
  -- False on the left can always be used.
  apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303713235215640224118294627043 : (p1 ∨ ((((((p3 ∧ p1) ∨ ((((p2 ∧ p5) ∧ (p5 → True)) ∧ p2) → p4)) → ((p5 ∧ False) → (False → (False ∧ p4)))) → p1) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204407419940526583211949655470 : (((p2 → (p3 ∧ (p2 ∧ p1))) ∧ p5) ∨ (p1 ∨ (((p3 ∨ p5) ∨ ((p4 ∧ ((p2 ∨ (p1 ∨ p4)) ∨ False)) ∧ p5)) ∨ ((p5 ∧ p3) → p3)))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783281454897514115779517644251 : (((p3 ∨ ((((p2 ∨ (p1 ∧ p5)) ∧ ((((p2 → ((p2 → p5) ∧ p4)) ∧ p1) ∨ p3) ∧ p3)) ∨ p5) ∨ (p4 ∧ ((p1 ∧ True) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604402935977967486848710032398 : ((((True → (p3 ∧ (True → (p2 ∨ (((p3 ∨ (((p5 ∨ (True ∨ p4)) ∨ (p4 ∧ p2)) → ((p2 ∧ p3) ∧ p1))) ∨ True) → False))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120679805397923962300031591925 : ((((p4 → ((p1 ∨ False) → ((p1 → ((((False ∧ ((p1 ∨ (p5 ∨ p2)) → p2)) ∨ True) ∨ p2) ∧ p2)) ∨ p1))) → p2) ∨ False) → (False ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p4 → ((p1 ∨ False) → ((p1 → ((((False ∧ ((p1 ∨ (p5 ∨ p2)) → p2)) ∨ True) ∨ p2) ∧ p2)) ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232149688133781279483566921564 : (((True → p1) → p3) → (p5 ∨ (((p2 ∧ (((p1 → p1) ∨ p1) → (p2 ∧ p2))) → ((True ∨ ((p2 → True) ∧ p5)) ∧ (p4 → p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



