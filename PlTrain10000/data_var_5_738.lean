variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196803093002530196373136282246 : ((((p3 ∧ True) → (p1 ∨ (p4 ∧ False))) ∧ True) ∨ (p5 ∨ ((p4 ∨ (p4 → (p5 ∧ p3))) ∨ ((False ∧ ((False ∨ (True ∨ p2)) ∧ p1)) ∨ True)))) := by
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
theorem thm_5_vars_69157349779034362592059834038 : ((p5 → ((((((False → p3) ∨ (((True ∧ False) ∧ False) ∨ p5)) ∧ ((p1 ∨ p4) ∨ p2)) ∨ False) → p4) ∨ (p5 ∨ (True ∨ (p4 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59059190390613841983742788132 : (((p4 ∧ p5) ∨ ((p2 ∨ (p4 ∨ ((True → p5) ∨ ((p1 ∨ (p3 ∧ (False ∨ p2))) → ((p1 → p5) → (p4 → p5)))))) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68698465260510479088249627478 : ((p4 → (((((p3 → p2) ∧ (((True ∨ (p5 → False)) ∨ ((True → (p2 → p5)) ∨ p4)) → (p1 ∨ p3))) → True) ∨ p2) → (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42195908166728809814211008879 : (((True ∧ ((p2 ∨ (False ∨ True)) → ((False ∨ ((((((p3 → (True ∧ (p2 ∧ p5))) ∨ p4) ∧ p4) → p3) ∧ p5) ∨ p3)) ∨ True))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731490646081836876465856816813 : ((((True → (p2 → p5)) → (((False ∧ (False ∧ p4)) ∨ ((p4 ∧ (p5 → True)) ∨ p1)) ∧ (((((p3 ∨ p5) ∧ p3) → True) → True) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249485093702588429530833671662 : ((p5 ∨ p1) ∨ (((p2 ∧ ((True ∨ p1) ∧ (((((False → (p1 ∧ True)) → (False → p4)) → (p1 → False)) ∨ p2) → False))) ∧ p1) → (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((((False → (p1 ∧ True)) → (False → p4)) → (p1 → False)) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : ((((False → (p1 ∧ True)) → (False → p4)) → (p1 → False)) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114643264286782697039971825229 : (((((((True ∨ ((False ∨ True) → (p3 ∧ False))) → p3) ∨ p4) ∨ False) ∨ (False ∨ p4)) ∨ (p2 → ((p4 ∧ p1) → (False ∧ p3)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258504747171064057483251271327 : ((p5 ∨ p2) → (p1 ∨ (p3 ∨ ((((p2 ∨ (p4 ∧ p3)) ∧ True) ∨ (p2 ∨ True)) ∨ ((p1 ∧ (p4 ∧ (p3 → p3))) ∨ ((p1 ∨ False) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185166771251467955932908997225 : (((False → True) → (p1 ∧ (((p2 → p4) ∧ False) ∨ (False → p5)))) ∨ ((True → ((p1 ∨ (False → ((p5 ∧ False) → p5))) ∧ (True ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646109380429676652468502100193 : ((((True → (p2 → ((p1 ∧ ((((p3 ∨ (p4 → p3)) ∨ False) → ((p2 → p2) ∧ False)) → (p2 → p1))) → ((p2 → p2) ∨ False)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317128943881148109345088299628 : (p3 ∨ (p5 → ((p2 ∨ False) ∨ ((False ∧ (p3 ∨ (p2 ∧ p5))) ∨ (p3 ∨ (((p5 → p3) ∨ (((False ∧ (p2 ∨ True)) → p2) ∨ p1)) → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61592386162653648905141647787 : ((p1 ∧ (((p5 ∨ p4) ∧ p3) ∨ (((p1 ∨ (p5 ∧ False)) ∧ (p1 ∧ (((True ∧ (p1 → ((False ∨ p3) → True))) ∨ p2) ∧ p1))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114706583204568088075288851443 : (((((p1 → p2) ∨ (((p1 ∧ p2) → (p2 ∧ p3)) ∨ (p1 ∧ (p5 ∨ p3)))) ∨ True) → (((p1 ∧ p4) → (p4 → p5)) ∨ True)) ∨ (p3 ∧ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52082566180007832599599066975 : ((((False → (((((True ∧ True) ∧ p1) ∨ (p5 ∨ (p1 ∨ p4))) ∧ False) → p3)) ∧ True) → (True ∧ (((p3 ∨ True) → False) → (p4 ∧ False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46960779258237154573152834539 : (((((False → (((((p1 → p4) → False) → ((p5 ∨ ((False → p5) ∧ False)) ∨ p2)) → (p2 ∧ True)) → p3)) ∧ True) → p3) ∨ (p1 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164727995915099465553991189169 : ((((True ∧ ((((p2 ∧ (True ∨ p1)) ∧ p2) ∨ (p1 ∧ (p5 → True))) → True)) → p1) ∨ True) ∨ (p3 → (p5 ∧ ((p2 ∨ (p2 ∨ p2)) → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111921955715252588307193090668 : (((((((p2 → p4) → (p3 ∨ p5)) → (p3 ∨ True)) → (p3 ∧ p2)) → (((p2 ∧ p3) ∧ (p3 ∧ (True ∧ True))) ∨ p3)) ∨ p5) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p4) → (p3 ∨ p5)) → (p3 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207221702011928548112790225020 : (((((p5 ∧ p3) ∧ p3) ∨ p4) ∨ p4) → ((p1 ∨ p1) ∨ (p2 → ((False → (p5 ∧ (p4 ∨ p3))) → (p4 ∨ (p5 → ((p1 → p4) → p3))))))) := by
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
      let h6 := h4.left
      let h7 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52479072342230228325650224086 : (((True → (((p3 ∧ ((p3 → False) ∨ ((p4 ∧ False) → p2))) → p5) → p1)) ∧ (True ∧ ((((p4 ∨ (True → p4)) ∧ p2) → p3) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216596086200056369196197611508 : ((((False → p2) ∧ True) ∧ p4) → ((((((p5 ∧ (p5 ∨ p4)) ∧ ((False → p5) → p4)) ∧ True) ∨ (p5 ∨ ((p3 → p3) → False))) ∨ True) ∧ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233773581544725110702735025905 : ((p3 ∨ (p3 ∨ p2)) → ((((((False ∨ p3) ∧ p4) ∨ (((p3 ∨ p1) ∨ p3) ∧ (p1 ∨ p5))) ∧ p1) ∨ p5) ∨ ((p2 ∧ p4) → (True ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135807875434395357895913214082 : (((False → ((p3 ∧ p3) ∧ ((p5 ∨ (p3 → p1)) → (p3 ∧ (True ∧ p4))))) → (p3 ∧ ((p3 ∧ (False → p3)) ∧ p5))) ∨ (False → (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229651942630593887671330119395 : ((p3 → (p5 ∨ p2)) ∨ (((False ∧ p4) ∨ (p5 → (p2 ∧ True))) ∨ ((False ∨ (p5 → (p1 → ((p5 ∧ p2) ∧ p2)))) → (True ∨ (True ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60470894722898065693541917228 : (((p5 → p4) → ((((p1 → (False ∨ p1)) → p4) → ((p3 → (p4 ∧ ((True ∧ (True ∨ p2)) → p1))) ∨ p4)) ∨ ((p3 → p5) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_328133071470132482307781045585 : (True → (((p3 ∨ p2) ∧ (((True ∧ (p2 ∧ ((True ∧ True) ∧ ((True → True) → False)))) → False) → (p4 ∧ (p4 ∧ p3)))) ∨ ((p2 → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303834345971242907942783264640 : (p1 ∨ ((((((((p5 → ((p4 ∨ p5) ∧ p4)) → (p4 → p2)) ∧ (p2 → p1)) ∨ ((p5 ∧ True) ∨ True)) ∧ p4) ∨ True) ∨ (p2 ∨ p4)) ∨ p1)) := by
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
theorem thm_5_vars_696332317845950116633438450608 : ((((p2 → (True ∨ ((True ∧ p1) ∨ ((False → (p2 ∨ p3)) ∧ (p5 → True))))) → (p3 ∨ ((p4 → ((p2 → False) ∧ (p4 → p4))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244536141359813119026419614092 : ((False ∧ p3) ∨ (False ∨ (p5 ∨ (p1 ∨ ((p1 → ((((True → p5) ∨ ((((True ∧ p4) ∧ p5) → True) ∨ p2)) ∨ True) → (True ∨ p1))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
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
theorem thm_5_vars_190335671212053266758198550912 : (((((True ∧ p1) ∧ p3) ∧ ((p3 ∨ False) ∨ False)) ∨ True) ∨ (True → ((False ∨ ((((False → p1) ∧ p2) → (True ∨ p4)) ∨ (True → True))) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778207836477958991506212599810 : (((p1 ∨ ((False ∨ p1) → (((((p4 ∨ p5) → (p1 → (p4 ∨ p3))) ∨ p2) ∧ (((p3 ∧ p3) ∨ p4) → p2)) ∧ ((p5 → p3) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157879140760014809430099898068 : ((((p1 → ((False ∨ p4) ∧ p3)) ∧ ((p3 ∧ False) ∨ p3)) ∨ ((p4 ∧ p3) ∧ (p4 ∧ (True → False)))) ∨ (((False ∧ p4) ∧ (False → p1)) → p2)) := by
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
theorem thm_5_vars_218311575778890266082083987392 : (((p5 ∨ p4) ∨ (p4 ∨ p2)) → (p1 → (((p2 → (True ∨ True)) ∧ (p1 → (((True ∨ (p5 ∧ (False → p1))) → p1) → (p1 → p2)))) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50080269358399692273271391835 : (((False ∧ (((p2 ∨ (True → (((p2 ∧ ((p1 ∨ p3) → p2)) ∧ False) ∨ (p4 ∧ p4)))) → p2) ∨ True)) ∧ ((p3 → (True ∧ p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199744620034128504383149420099 : (((p4 ∨ (((False ∧ p3) ∨ p4) ∧ p4)) → p4) → (p4 ∨ ((True → (True → ((p1 ∧ (p5 ∧ p4)) ∧ (((p1 ∨ p3) → p5) ∧ p3)))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171799230155360415327073255979 : (((((p3 ∨ ((p4 → (False → p3)) → p5)) ∧ p2) ∨ ((True → p1) → False)) → p4) ∨ (p3 → ((p1 ∧ p4) → (((p5 ∨ p4) ∨ p3) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192885265911806773628804731946 : (((p4 ∧ ((p1 → False) ∧ (p4 ∨ p4))) ∧ (p1 ∧ True)) → (((((True ∧ p5) ∧ ((((p4 ∨ p5) ∧ p4) → p5) ∧ p5)) ∨ p2) ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46719658445571780788106948283 : (((p5 ∨ (True ∧ (p1 → (((p2 ∨ (((p3 ∧ ((True → p3) ∧ (p4 ∨ p2))) ∧ True) ∧ p3)) ∨ (p1 ∨ False)) ∨ p4)))) ∧ (p2 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747859224496367392657775623320 : ((((False → p3) → (p5 ∧ ((((p1 ∨ p5) ∨ p4) → (((p5 ∨ ((p4 ∨ True) → (p3 ∧ (p4 ∨ (p1 ∨ p3))))) ∨ p4) ∧ True)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59760892449556026752377702653 : (((p1 ∧ p4) → (((p4 ∧ (p2 ∧ ((p4 → (p3 → p3)) ∧ (((p5 ∨ p2) ∨ (p5 ∨ (p3 → (p5 ∨ p5)))) ∨ p3)))) → p5) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50430134562639974968603709369 : (((p5 ∧ (((p5 ∧ (p4 → p4)) → ((True ∧ p3) ∨ (((p2 → True) ∧ p2) → (p3 ∨ p3)))) → p5)) ∨ ((False ∧ (p2 ∧ False)) → p1)) ∨ p3) := by
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
theorem thm_5_vars_49928429634993687084737499377 : ((((p4 ∧ (((p4 → p4) ∨ (((p2 ∨ p3) ∨ True) → p1)) ∧ (((p3 → True) ∧ p5) → False))) → p5) ∧ ((p2 ∨ (True ∨ True)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61055859122751280258837703211 : ((False ∧ ((p3 → (((False ∧ ((True → ((p2 → False) ∨ p2)) ∧ False)) ∨ (p2 ∧ (p1 ∨ True))) ∨ ((True ∧ False) ∨ p4))) → (p5 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324708244577010305549287278584 : (p5 ∨ (((p3 → p1) ∧ p5) → ((((((p3 → p1) ∨ ((p1 ∨ ((p3 ∧ (True ∨ (True ∨ False))) ∨ False)) ∧ p5)) ∨ p4) → p1) → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_698203053621667018302729385520 : ((((((False ∨ (False → p4)) ∧ (p1 ∨ (p2 ∧ (p4 → False)))) → p3) ∨ (((p4 ∨ (p1 → p5)) ∧ ((p2 ∧ p1) ∧ p2)) → (p2 ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231149783923051236898408086865 : (((p1 ∨ p5) ∨ p5) → (((False ∨ False) ∧ ((p2 ∧ (p4 → False)) → ((p3 → p4) ∧ (((p3 ∨ True) ∨ (p1 ∧ p5)) ∧ (p3 → p5))))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60048612354690935864268837023 : (((p2 ∨ True) → ((((p1 ∧ (((p2 ∨ (p3 ∧ (p1 → False))) ∧ ((False ∧ p2) ∨ False)) → (False ∨ True))) ∧ p1) → p3) ∧ (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42190729741609966858452590209 : (((True ∧ (((False → (p4 ∨ ((p4 ∨ (False ∨ p2)) ∨ p5))) ∨ False) → ((p1 → ((p3 ∧ (p5 → True)) → (p5 → p2))) ∨ False))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135082991119670238094740845224 : (((((p1 ∧ (p3 → (False → p4))) ∧ (((p4 → True) → p5) ∨ (p5 ∨ p1))) → ((p5 ∧ p4) → False)) ∨ (True ∨ p3)) ∨ (True ∧ (p3 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41284810389619482241193393563 : (((((((p3 → p1) ∨ p3) → (True ∧ (p1 ∨ (True → (True ∧ True))))) ∧ (p2 → (True ∨ p5))) → ((True ∨ p4) ∧ (p1 ∨ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199586088446980038061429408104 : ((((((p4 ∧ p1) ∨ p5) ∧ p3) → p4) → p5) → (((((p4 → (p5 ∧ (((False → p4) ∨ False) → p2))) ∧ (p4 → p2)) ∨ True) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135931147614772616840150897074 : (((p5 → ((((p4 → p2) → ((True → p3) → p2)) ∨ True) → p3)) → (p1 ∨ (p3 → (p3 ∧ ((p5 ∧ p4) ∧ p5))))) ∨ ((p2 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199667014293488373480507128755 : ((((False ∧ p1) ∨ (p3 ∧ (False ∨ False))) → p5) → ((((p5 → ((p1 → p3) → p3)) → p4) ∧ (((True ∧ p2) → p2) ∨ p1)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310208335622041883258944233807 : (p2 ∨ (((((p4 ∧ p5) ∨ (p5 ∨ True)) ∧ (False ∨ p3)) ∧ (p4 ∨ p1)) ∨ (p4 → ((p1 → ((p2 ∨ (p3 ∧ True)) ∨ (p1 ∧ False))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44867254081585318041967140343 : ((((p1 → (p3 → p2)) ∨ ((((p4 ∧ p3) ∧ (p2 → (p3 ∨ ((p5 ∨ True) ∨ ((p5 ∨ p3) ∨ True))))) → (True ∨ False)) ∨ False)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200272205819140561234088716644 : (((p3 ∨ (p2 ∨ False)) → ((p4 ∧ p1) ∧ p3)) → ((((((p2 → p5) → ((((p4 → True) ∨ p3) → p2) ∨ p5)) → p4) → p3) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53122110092806032696711450612 : (((p5 → ((p4 ∨ (((p3 ∧ p2) → False) ∨ (True ∨ p5))) → p3)) ∧ (((((True → p1) ∧ (False → p4)) → (p3 ∧ False)) ∧ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32015612418423185081314911700 : ((p1 ∨ ((p5 ∧ (((True ∧ p3) → (p2 ∨ ((p4 ∨ (p1 ∨ ((p3 → True) ∧ p2))) ∨ ((p2 ∨ (True ∧ p1)) ∨ p2)))) → p3)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_59895145669303633690592665445 : (((p5 ∧ True) → (p5 → ((((p1 → ((p1 ∧ (p2 → p4)) ∨ p4)) ∧ False) ∨ False) ∨ (((False ∧ (True ∧ True)) ∨ (False ∨ p1)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65820565941727404078761687808 : ((p4 ∨ ((((p2 → (p3 → p1)) ∨ p3) → p1) → ((((p2 ∨ (((p3 ∨ p1) ∧ False) ∧ p5)) ∨ (p3 ∧ p2)) ∨ True) ∨ (p3 → True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_152118176141101195465091255503 : ((((p3 ∨ (p2 ∨ (p5 → (False ∨ p1)))) → False) ∧ ((((p3 ∨ p2) ∨ ((p5 ∧ p5) ∧ p1)) ∧ True) ∨ p2)) → ((p1 → p5) ∨ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (p3 ∨ (p2 ∨ (p5 → (False ∨ p1)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : (p3 ∨ (p2 ∨ (p5 → (False ∨ p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4450616600419113624989531434 : (p2 → ((((False ∧ p4) → (p2 ∧ True)) → (((p2 → p4) ∨ ((p4 ∧ p1) ∧ (p2 ∨ True))) → (p3 ∧ (False ∨ (False → p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227814212331906603152757404561 : ((p2 ∧ (False ∧ p3)) ∨ (False ∨ ((((False ∧ (p3 ∨ p5)) ∨ p1) ∨ ((False → (p5 ∨ p2)) ∧ (p5 → (p4 ∨ True)))) ∧ (True ∨ (p3 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640609676662478998488314246666 : (((((p1 ∨ p1) ∧ ((((True ∧ p5) → (p4 ∨ p2)) ∨ ((False ∨ ((p2 ∨ p4) → (p5 → p2))) → p3)) ∨ (p5 ∨ (p5 → p4)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43858053284432593512596140724 : ((((((p4 → p3) → (p4 ∨ (p3 → (((False ∧ p3) ∧ p5) → (p1 ∨ True))))) → (p2 ∧ (False ∧ (p1 ∧ p3)))) ∧ (p1 → p5)) → p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p3) → (p4 ∨ (p3 → (((False ∧ p3) ∧ p5) → (p1 ∨ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117351262976392472439585320623 : ((False ∧ (p2 ∧ ((p4 ∧ (p4 ∧ ((((p2 → (p4 ∨ (p3 → p5))) → ((False ∨ (False → p2)) → p5)) → p2) → p3))) ∧ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748547136229192110972770534674 : ((((p3 → False) → ((p4 → (False → ((p1 → p1) ∧ (((((True ∧ p2) ∧ ((p1 → True) ∨ (p5 → p2))) ∨ p2) → True) ∨ p5)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59043433454962728139645913107 : (((p4 ∧ p2) ∨ ((p5 ∨ (True ∧ (False ∨ (p3 ∨ (True → True))))) ∨ (True → ((((p3 ∨ p1) ∨ (False → p2)) ∧ False) ∧ (p5 ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780090731810871291556029219740 : (((p2 ∨ (((True ∧ (((True ∧ (p1 ∧ (p1 ∨ ((p4 → p4) ∨ (p1 ∨ p2))))) → False) → False)) ∧ (p4 ∨ (p1 ∧ p1))) → (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309942443577314974630707963921 : (p2 ∨ ((p1 → ((p4 ∧ ((True ∨ p5) → (((p4 → (p5 → False)) ∧ (p3 ∨ True)) ∨ p2))) ∧ p5)) ∨ (((p1 ∧ p3) → p5) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134087058641571446161689082390 : ((((((p5 ∧ False) ∨ p4) → ((p1 ∨ ((p1 ∧ p2) ∨ p5)) ∧ (((p1 → p1) → p3) ∧ (p2 → p1)))) → p5) ∨ True) ∨ (True → (False ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258704082221529225422412886160 : ((True → True) → ((((((True → p4) ∧ True) ∨ p1) ∨ (p1 ∨ ((p1 ∨ p2) ∧ (True ∨ p2)))) → (((p1 ∧ (p5 → p1)) → p3) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135014920024130839358170523590 : (((p4 ∨ (False ∨ (((p1 → p3) → (((p3 ∨ p4) ∧ (p5 ∧ (p5 → False))) → p4)) → (p3 ∨ p1)))) ∧ (p1 ∧ p5)) ∨ ((p2 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123629765560638497620250167720 : ((((((((True ∧ (p2 ∨ True)) ∨ ((p3 ∧ True) ∨ p5)) → p5) ∨ p5) ∨ False) ∨ False) → (p1 ∧ (p3 → ((False ∨ p4) ∨ p4)))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617946955290885681699117909372 : (((((p5 ∨ ((p2 ∧ p5) → (p4 ∨ p2))) → ((((p1 ∨ (p1 ∧ (p4 ∧ True))) ∧ (False ∧ (p1 ∨ p5))) → (False ∧ p3)) → p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_351272037354628529451862284515 : (p4 → ((((((p3 → (False ∨ ((p2 ∧ False) ∧ (p2 → (p1 → p5))))) → (True → (True → True))) ∨ p1) ∨ p3) ∧ p3) → (p2 ∨ (p1 ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206302857753620772686723868623 : ((p1 ∨ (((p3 ∧ p3) → p2) → p3)) ∨ ((p5 → ((False → p3) ∨ p4)) → (((True → (p5 ∨ p3)) → True) ∨ ((p5 → True) → (p4 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199769783940251733376111028569 : (((p2 → (p3 ∧ ((p5 → p4) ∧ p2))) → False) → ((True → (((False ∧ False) ∧ (False ∧ (p5 ∧ (True ∨ p4)))) ∧ p5)) ∨ ((True ∨ p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210172415350617534909519909444 : ((((p1 ∨ p5) ∨ p2) ∨ True) ∧ (p1 ∨ (((((((p2 ∨ ((p4 ∨ p2) → p3)) ∧ p3) → p3) ∨ False) → ((p3 ∨ p3) ∧ True)) ∨ True) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310777966309172079017400377750 : (p2 ∨ (((p5 ∧ p5) ∨ p2) ∨ ((((((((p2 → ((p3 ∧ p2) ∧ p1)) → (p5 ∧ p1)) → p2) → True) ∧ False) → p4) → (p1 → p1)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112603986768541117841511024005 : (((((True ∨ (((p5 → False) ∧ p5) ∨ ((p3 ∨ ((False → True) → False)) → ((p2 ∧ p4) → p1)))) ∧ True) ∨ (False → p3)) → p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585998341543836653054562596468 : ((((((True ∧ ((((True ∧ p1) → (((p3 ∨ ((True ∨ p4) ∨ False)) ∨ p5) ∨ p2)) ∨ p5) → p5)) ∧ ((p5 ∨ False) → p1)) ∧ True) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347016686136319144206071686732 : (p3 → (((((p5 ∨ p4) ∨ p5) → p5) ∨ ((p2 ∨ p2) → ((p4 ∨ p1) ∨ (p2 → p2)))) ∨ (((((p5 → p1) → p3) ∧ False) ∧ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592383112053646865616688388225 : (((((((p2 ∨ p3) → (p2 → (True → (((False ∨ p5) ∨ p2) ∧ (p4 ∧ True))))) ∨ (p2 ∧ (p5 ∨ (True → p4)))) → (False ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891686961060317128754766896597 : ((((((p5 ∧ ((p4 ∧ (p3 ∨ p2)) ∨ (((((False ∨ (p5 ∨ False)) ∨ p5) ∨ False) ∨ p5) → p4))) ∧ True) ∧ p1) ∧ (p3 → (False ∨ True))) → p4) ∧ True) := by
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
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : ((((False ∨ (p5 ∨ False)) ∨ p5) ∨ False) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678445306828536780614312674191 : (((((p2 ∨ ((p1 ∧ p5) ∧ False)) ∨ (p5 ∧ (((p4 → True) ∧ p2) ∨ (p1 ∧ (p5 ∧ (p4 ∧ p3)))))) ∨ ((True → p5) → (p1 ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181029960167098220890407496127 : (((p1 → p4) ∨ ((((p4 → False) → ((p5 → p2) ∨ p4)) ∧ p4) ∨ p5)) → (False ∨ (p1 ∨ (True ∨ ((p3 ∨ True) → ((False → p4) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160661725356516250788690957741 : ((((p3 → True) → (p2 ∧ (p2 → ((p4 ∨ p3) ∨ p2)))) → (((False → False) ∧ p1) → (p2 ∨ p1))) → (p2 ∨ ((False ∧ (True ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126831547687966060812571634657 : ((p5 ∧ ((p5 ∧ (p1 ∧ ((p5 ∨ (True ∧ (p4 ∧ (p1 ∧ (p3 ∨ p1))))) → False))) ∧ (True ∨ (p1 ∨ ((False → p5) ∧ p1))))) → (p5 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h24 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h25 : (p5 ∨ (True ∧ (p4 ∧ (p1 ∧ (p3 ∨ p1))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h26 := h23 h25
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h29 : (p5 ∨ (True ∧ (p4 ∧ (p1 ∧ (p3 ∨ p1))))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h30 := h23 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h34 : (p5 ∨ (True ∧ (p4 ∧ (p1 ∧ (p3 ∨ p1))))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h35 := h23 h34
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762934961743900641182786166980 : (((p3 ∧ (((p4 ∧ p3) ∨ (p4 ∧ p5)) ∧ (((p5 → (False → (p3 ∧ ((p3 → p2) ∨ p5)))) ∨ p5) ∧ (True ∧ ((p5 → p4) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245281390194158995669401116036 : ((p2 ∧ p2) ∨ (((((p5 → ((p3 ∧ (((p1 ∨ (p3 → p4)) ∧ ((p2 ∧ (False ∨ p3)) ∧ p4)) → True)) → p4)) ∧ p5) → p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338956067842459638195241064688 : (p1 → ((False → p1) → (((((p4 ∨ (((p2 ∨ True) ∧ (False → (p2 ∧ p4))) → (p4 → (p4 ∨ p5)))) → p3) → (p1 ∨ p2)) → p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113729648606946325017713640535 : ((((p2 → ((((False ∧ p1) ∧ p1) → ((p2 ∧ ((True ∨ True) ∧ True)) ∧ p5)) ∧ p5)) ∨ ((p3 ∨ p4) → p2)) → (p5 ∧ p1)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137626649199632604484853690029 : ((False ∨ (((p1 ∧ p1) → ((p5 ∨ ((p2 → ((False → p2) ∧ p3)) ∨ ((True ∨ p2) ∨ p5))) ∨ (p4 ∨ False))) → p3)) ∨ (p4 → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65886293968714065975758276543 : ((p4 ∨ ((p2 → False) → ((p1 → ((p4 ∨ p1) → ((((p3 ∧ (((False ∨ True) ∨ p4) → p3)) ∨ True) ∨ p5) ∨ (False → False)))) ∨ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59245266306602349712487901754 : (((p2 ∨ p3) ∨ (((((((p3 ∧ p1) ∨ True) → True) ∨ False) ∨ p5) → ((p2 ∧ (p2 ∧ p1)) ∨ p1)) ∨ ((p5 ∨ (True ∨ p2)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179404808022870091201115145398 : ((p3 ∨ (p3 ∨ ((True ∧ (((p1 ∨ p4) → False) ∨ (False ∨ True))) ∧ True))) ∨ ((p3 → (p2 ∨ (((p2 → p2) → p5) ∨ p5))) → (p5 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634379769038892536104912521320 : ((((((p3 → (((((p1 ∧ (p4 ∧ (True ∧ (p5 ∧ (p1 ∨ p5))))) → p5) ∨ p1) ∧ True) → p4)) ∧ p1) ∧ (p5 ∨ (p4 ∨ p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809751897599371085148276269713 : (((p5 → (((((p4 → (False ∨ (True ∧ False))) ∨ ((p1 → ((False → p1) ∧ (p5 ∧ p5))) ∧ p3)) ∨ (p1 ∧ p2)) ∨ p1) ∨ (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116997603578193052078745682266 : (((True ∨ p4) → ((p4 → (p1 ∨ (p1 ∨ ((True → (p3 → (True ∧ p1))) ∨ p2)))) ∧ (p5 ∨ (p4 ∨ (p3 ∧ (p5 → p2)))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



