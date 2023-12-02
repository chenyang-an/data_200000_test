variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725961269423390112488950222201 : (((((p3 → p2) ∧ p4) ∨ (p5 ∧ (p5 ∧ ((p3 ∧ ((p2 ∧ (p2 → (p2 ∨ ((p2 ∨ (p3 ∨ p1)) ∧ (True → p5))))) → p3)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739260248917844323389080668643 : ((((p4 ∧ p2) ∨ (((p2 ∧ (False → (((p2 ∧ (p1 ∧ ((p1 ∨ p5) ∨ (True → p5)))) ∨ p1) ∨ p3))) → (True ∧ p3)) → (p5 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149075530746100015792569705577 : ((((False ∧ True) → p5) → (((p3 → ((p1 ∧ (p4 ∨ (p3 ∧ (p2 ∨ p1)))) ∨ False)) → (p5 ∧ True)) ∨ True)) ∨ (((p5 ∧ p2) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694288415129648036611198790589 : (((((p3 ∨ (p2 ∨ p3)) ∧ (True ∧ ((p5 → p2) → ((p1 ∨ p2) → False)))) ∨ (False → ((p5 ∧ (p2 ∧ p4)) ∨ ((p1 ∧ p4) → p1)))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_152994600355781268559499733574 : ((p1 ∧ (True ∨ (((((p1 ∨ ((True ∨ p1) → (p5 → p4))) ∨ (p4 → p5)) ∨ True) ∨ p2) ∧ (False → p5)))) → (p2 → ((p2 → p4) → p4))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h16 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h2
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h17 := h3 h16
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h19 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h2
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h20 := h3 h19
            -- One of the premise coincides with the conclusion.
            exact h20
        case inr h21 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h22 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h23 := h3 h22
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h24 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h25 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h25
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h28 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h29 := h3 h28
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313102060345035516238445895385 : (p3 ∨ ((((((p3 ∧ ((((True → p4) → p2) ∧ (((p2 ∧ False) ∨ p2) ∧ p2)) ∧ p3)) ∧ True) ∨ True) ∨ False) ∧ (True ∨ (True ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692486315796000319779524900554 : (((((((True → ((p5 ∨ p1) ∧ (True → p3))) → True) → True) ∨ (True → p1)) ∧ ((p2 ∨ p4) ∨ ((p1 → (p1 → False)) → (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748398207567120885470130805209 : ((((p2 → p3) → ((p4 ∨ ((True ∧ (p4 → (p5 → False))) ∨ (p5 ∨ p4))) ∧ (p1 ∨ ((True → p3) → ((False → False) → (p3 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67326006572599562840743927106 : ((p1 → (((((((p1 ∨ (p4 → p3)) → ((((p5 → p2) ∨ p1) ∧ (p5 → p2)) → p2)) → p5) → True) → (p2 → False)) ∨ True) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157614812753374739351132940814 : ((((((p5 ∧ p5) ∨ (p2 → False)) → ((p2 ∨ p2) ∧ (p5 → p3))) → p4) ∧ (True → (p5 → True))) ∨ ((p1 → (False ∨ True)) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4302102524844064063171466155 : (True → ((p3 ∧ p2) → (((p1 ∨ (p2 → ((p4 ∨ (p1 → (p3 → (((p1 ∨ p1) ∨ p4) ∧ p2)))) → p1))) ∨ (True ∧ True)) ∨ p2))) := by
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
theorem thm_5_vars_262359581465056513965472935368 : (True ∧ ((((p5 ∧ False) ∨ p2) ∨ (((p3 ∧ p4) ∨ ((p5 ∧ (True ∧ p1)) ∧ p4)) ∨ ((False → (((True ∧ False) → p2) → p3)) ∨ p3))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718239723392870041755545187678 : (((((p1 → (True ∧ p2)) ∨ p2) ∨ (p1 ∨ ((p4 ∧ ((((p3 ∨ ((p3 ∨ p2) ∨ False)) → (False ∨ p1)) → (p2 ∧ p1)) ∨ True)) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148601829127490124827346507333 : (((p4 ∨ ((((p2 ∨ True) ∧ False) → p1) ∧ (p5 ∧ p5))) ∨ ((p4 ∨ p2) → ((p4 → p5) → (True → p4)))) ∨ (p3 ∨ ((p4 → True) ∨ p3))) := by
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
theorem thm_5_vars_660308762314116374607008245448 : (((((p3 ∧ ((((p1 ∨ p3) → True) ∧ p2) ∨ (p2 → (p5 ∧ ((True → (p3 → ((False ∧ True) → p3))) → p5))))) ∨ False) → (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41983021218021221428785491065 : ((((p3 ∨ p5) ∧ (((((True → (p5 ∧ p1)) ∨ True) ∨ p1) → (((p1 ∨ ((p5 ∧ (p2 ∨ p2)) ∧ p2)) ∧ False) ∨ p2)) ∨ p3)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139679523849182631835650585435 : ((((False ∧ (False → p1)) ∨ (((((p2 ∨ (True ∨ (False ∨ False))) → p4) → ((False → False) ∧ p1)) ∧ p2) → p3)) → p2) → (p1 → (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157163023782870297729297635942 : ((((True → (p2 ∧ ((((True → p3) ∨ False) ∧ p3) ∨ (p3 ∧ (p4 ∧ (False ∨ True)))))) ∨ True) → False) ∨ ((p2 ∨ (p1 ∨ (p4 ∨ True))) ∨ p3)) := by
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
theorem thm_5_vars_184658853927977041504898463315 : ((((p5 → (True ∨ (False ∨ p4))) → False) ∨ (p1 ∨ (p4 → p2))) ∨ (p5 ∨ ((((p5 ∧ False) ∧ p3) → p3) ∨ (p5 ∧ (p1 → (p5 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181577654315424090459688591751 : ((p1 → ((((p1 ∨ p3) ∧ (p2 ∨ (p4 ∧ (p2 ∧ p5)))) → p2) ∨ False)) → ((((((p4 ∧ p1) → False) ∧ (False ∧ p1)) ∨ p3) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219372767222874755511170878919 : ((p3 ∨ ((False ∧ p4) → p2)) → ((p3 ∨ (p4 → p4)) ∧ ((True → ((p1 ∨ True) → p2)) ∨ (p3 → (((False ∧ p2) → (p5 ∧ p5)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
    -- Conjunctions on the left can always be decomposed.
    let h17 := h14.left
    let h18 := h14.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190468563655531360790387345216 : (((((p3 ∨ (p4 ∨ (p1 ∧ True))) → p5) ∧ p3) → p1) ∨ ((True → (((p1 ∨ True) → (p2 ∧ (((True ∧ p2) → False) ∧ p1))) ∧ p3)) → p2)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358116320225656050661989547153 : (p5 → (p2 ∨ (((((True → (((p1 ∨ p4) → p2) → (False → p5))) → p5) → p3) → p4) → (((False ∨ ((p1 → p4) → p3)) ∧ p1) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307294302980423620747871117997 : (p1 ∨ (p2 ∨ (p5 → (((((((False ∨ p4) ∨ (p1 ∨ ((p4 → p3) ∨ p4))) ∨ p5) ∧ (True ∨ p5)) → p4) ∨ p4) ∨ ((p2 ∧ p3) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311293180520848502909152364709 : (p2 ∨ (True ∧ ((True → False) → (p3 ∨ ((((True ∧ (p1 ∨ p1)) ∨ True) ∧ p5) → ((((p4 → p3) → (True → p2)) ∧ (p5 ∨ p4)) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_604792807014839027654887206235 : ((((p1 → (((((p1 ∧ True) → (p2 ∨ p3)) → (p4 ∨ ((True ∧ (p4 → (p1 → True))) ∨ (p5 ∨ (p2 → True))))) ∨ True) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325132699296950490275927246828 : (p5 ∨ (True ∧ ((((p4 → (p3 ∨ p2)) ∧ (True → (False ∨ ((p3 ∧ (p3 ∧ p2)) ∧ False)))) ∧ (((p5 ∨ p5) → p4) → (p4 → p2))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136904481243576391154382480516 : (((p5 ∨ p3) ∨ (p4 ∧ (True ∧ (p4 ∧ ((p4 ∨ (p4 → p3)) → ((p4 → p3) ∧ ((p2 ∧ True) → (p4 ∨ True)))))))) ∨ (p1 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244748338670096489045141904314 : ((p1 ∧ False) ∨ (((p1 ∨ ((p1 ∨ (p2 ∨ p5)) ∨ (((((p4 ∧ True) → p3) → p3) ∨ True) → ((p4 ∨ p5) ∨ p4)))) ∨ p1) → (p2 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
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
theorem thm_5_vars_56584477023217552530599467094 : (((p1 → (p5 ∧ (False → p4))) → ((True → p3) → ((((p5 → p2) → ((p3 ∧ p5) → False)) ∧ (p1 ∧ p3)) → ((p5 ∨ True) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115279616816082834383468133849 : (((True → (p3 ∨ ((((False ∧ p1) → True) ∧ False) ∨ p3))) ∨ (p4 → (p2 ∨ ((False → ((True → p5) → (True ∨ p5))) → p1)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190274830112475921750821555395 : ((((False ∧ (((p1 ∨ p4) ∧ True) ∨ p1)) ∨ p5) ∨ p4) ∨ (False → ((False ∧ ((((p2 → True) ∧ (p3 ∧ (p1 ∨ p3))) ∧ p4) → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302001903280953538610926587038 : (False ∨ ((p5 → p3) → (True ∧ ((((p1 ∧ p5) → True) → ((((p5 ∨ p3) → p1) ∨ True) ∧ ((p4 → p1) → p2))) → ((p1 ∨ False) → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 ∧ p5) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p4 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783143828335365577343425568504 : (((p3 ∨ (((p4 ∧ p4) ∨ (p1 → (p4 → (((p1 ∨ (p5 ∧ p4)) → ((True → (False ∨ p3)) → p2)) → p5)))) ∧ ((p5 → p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58278356906095017785966014520 : (((True ∨ True) ∧ ((((p2 → (True → p4)) ∧ True) ∧ (False ∨ ((p2 → False) → p2))) ∧ ((p5 ∨ (True → (p4 ∨ p4))) → (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356027698696913392724450562864 : (p5 → ((((p5 ∨ p2) → (((p5 ∨ (p2 → p4)) → (p3 ∧ p2)) ∨ p4)) ∨ ((p2 ∧ p1) ∨ (p5 ∧ True))) ∨ ((p3 → (p2 ∨ p1)) ∧ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231254759141705849080483897513 : (((p4 ∨ p3) ∨ p2) → (False ∨ ((((p4 → False) ∧ (p2 ∧ True)) ∧ ((p2 ∧ p5) ∨ p2)) → (p4 → ((True ∧ ((False ∨ False) ∨ False)) ∨ p1))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h16 := h8 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h18 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h19 := h8 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h32 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h33 := h25 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h35 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h36 := h25 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h38
    -- Implications on the right can always be decomposed.
    intro h39
    -- Conjunctions on the left can always be decomposed.
    let h40 := h38.left
    let h41 := h38.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h40.left
    let h43 := h40.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h49 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h50 := h42 h49
      -- False on the left can always be used.
      apply False.elim h50
    case inr h51 =>
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h52 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h53 := h42 h52
      -- False on the left can always be used.
      apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45680393287190907025061545152 : (((p5 ∨ ((p3 ∨ (p2 ∨ ((p2 ∨ p1) ∨ p1))) → (((False ∨ p3) → (p5 → ((p1 ∨ (True → (p5 ∨ p2))) ∧ True))) ∧ False))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337360659931159905666335075565 : (p1 → (((((p3 → (p2 ∨ p4)) ∨ p5) ∧ (((p4 ∧ True) ∨ p2) → ((p1 ∨ False) ∧ p3))) ∧ (p1 → (p3 ∨ True))) ∨ ((p4 ∧ p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112059578041392659375865916357 : ((((True ∨ True) ∧ (False ∨ ((p2 ∧ p2) ∧ (((False ∧ p1) → (False ∨ (False ∧ p5))) → (False → ((p4 → p3) ∧ True)))))) ∨ p4) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159641612377167707166434618935 : (((((p5 ∨ p4) ∧ ((((p4 ∨ p4) → True) ∨ (p3 ∧ (p3 → (p5 ∨ p2)))) ∨ True)) ∨ p4) ∨ p3) → (p1 → (p2 ∨ ((p3 ∨ False) ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299952691431282444900304328853 : (False ∨ (((p1 → (((((p3 ∧ p3) ∧ ((True → p1) ∧ p3)) ∨ p2) ∧ (p3 → (p5 ∧ False))) → (p2 ∧ (p2 ∨ False)))) ∨ True) ∧ (True ∨ False))) := by
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
theorem thm_5_vars_135444598575688320547665335825 : ((((((p5 → (p3 ∨ p3)) ∨ p2) → (((True ∨ p1) → (p2 → (p3 ∨ p5))) → p1)) ∧ True) → ((p1 ∧ p1) ∨ p5)) ∨ (False → (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191810144580508765864628711672 : ((p2 ∨ ((p2 ∧ p1) ∨ ((p2 ∧ (p1 ∨ p1)) ∧ True))) ∨ ((((p3 ∧ False) ∨ ((False ∧ False) ∧ ((p4 ∨ False) → p5))) ∨ True) ∨ (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244587483938775305546332819036 : ((False ∧ p4) ∨ ((p4 ∨ False) ∨ (((p1 → p3) → ((True → True) → ((((True ∧ p5) ∧ p3) ∧ p2) → p3))) ∧ ((p3 → p3) ∨ (True ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338380479711174147200580637462 : (p1 → ((p3 ∨ (False ∨ (p1 → p4))) ∨ ((p3 ∨ p1) → ((p2 ∨ ((p4 → p5) ∧ p5)) ∨ (((False → p3) ∨ ((p5 ∨ p3) ∨ p2)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162405349070030479476626984499 : (((((((p3 → p5) ∨ (p2 → p4)) ∧ False) ∧ (False ∧ p5)) ∨ (p1 ∨ (p3 ∨ p3))) ∨ True) ∧ (False → (p1 → (p1 ∨ (False ∨ (True ∨ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315481078116916709169038907992 : (p3 ∨ (((p4 ∨ p2) → p1) → (((((p3 ∧ (p4 ∨ (p5 ∨ False))) ∧ p2) ∧ (p5 ∨ (p5 ∨ p2))) ∧ ((p2 → p4) → p1)) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_179853636717077229226186996020 : (((p5 ∨ (((p4 → p3) ∨ (((True → p4) → p4) ∨ False)) ∨ False)) ∧ p2) → ((p4 ∧ ((True ∨ (p5 → False)) → p3)) ∨ ((p1 → False) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
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
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37649078143586193709163761134 : (((((((p2 ∨ ((((((p3 → p1) → p5) ∧ p5) ∧ False) ∨ (p1 ∨ ((p4 ∨ p5) ∨ p3))) → True)) → p1) ∧ p1) → True) → p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152325258518969087488176619484 : (((True ∧ ((p2 ∨ p5) ∨ p2)) ∧ (((True ∧ p1) ∨ (p2 ∨ (((p2 ∧ p4) → (True ∧ p2)) ∨ p3))) ∨ p3)) → (((False ∨ p2) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178705389000078455101619564684 : (((p4 ∧ ((p5 ∨ True) → False)) ∨ (False ∧ (True → ((False → p5) ∨ p3)))) ∨ ((p5 ∨ (True ∧ True)) ∨ (p2 ∧ (p2 → ((p4 ∧ p5) → p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647742553510351585077955549414 : ((((p5 → (p3 ∨ (p2 → ((True ∨ True) → (p2 ∨ (((p5 ∧ True) → ((True ∧ False) → False)) ∨ (p4 → ((p1 ∧ False) ∧ p3)))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115576864684186271246498887826 : (((((False ∨ True) ∨ p4) ∧ (p2 → p4)) ∧ (((p5 ∧ ((((p4 → p4) → True) → p5) ∧ ((p4 ∨ False) ∨ p4))) ∨ p3) ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147881835810886900389384231623 : (((p5 → (p3 → ((p3 ∧ (False → (p3 ∨ (p3 → (False ∧ ((p3 ∨ True) ∨ p1)))))) → (p2 → p3)))) → False) ∨ ((p5 ∧ (p3 ∧ p4)) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184415289178722495562761960812 : (((((p3 ∨ (p5 ∧ (True ∧ True))) → True) → p3) ∧ (p2 ∧ False)) ∨ (((p5 ∧ True) ∧ ((((p5 ∧ p4) → False) ∧ (p1 ∧ False)) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52456253214708602178040275896 : (((p5 ∧ ((False ∧ p3) ∨ (((p3 ∨ ((True → p5) → p2)) → p1) ∨ True))) ∧ (((((p2 ∨ True) ∧ p4) ∨ (p5 → p4)) ∧ p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45969000973423872026997795971 : (((p5 → (p5 ∨ (((((False ∧ ((p5 → p1) → (p2 ∧ p2))) ∨ (p5 ∨ (p1 → (p2 ∨ True)))) ∧ p5) ∧ (False → p4)) ∧ p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304402552241233064975983436627 : (p1 ∨ (((p1 → (p1 ∨ p1)) → (((((True ∧ p5) ∨ (False ∧ True)) → (p1 ∨ p1)) ∧ p4) ∧ (((True → (True → p1)) ∧ p5) ∧ True))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p1 ∨ p1)) := by
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
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341583594329105345417232278529 : (p2 → (((((p1 → p1) → ((False ∨ ((p4 ∨ True) → p2)) → ((p2 ∧ p1) → p5))) → (p2 ∧ p1)) ∨ (p4 ∨ (p2 ∨ p3))) ∧ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160960274661446754302500356514 : ((((False → False) → False) ∧ ((p2 ∧ ((p2 → ((p3 ∨ p1) ∨ ((p5 ∨ p5) → p4))) ∧ p2)) → p5)) → (p5 ∧ ((p5 → p3) ∧ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h17 := h13 h15
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133675794830433959702652439645 : ((((True ∨ ((((p4 ∧ ((p3 → True) ∨ p5)) ∧ (False ∧ (p5 ∨ p3))) ∨ (p4 ∨ p1)) → p5)) → (p4 → p2)) ∧ True) ∨ ((p4 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137989491706347424905164039581 : ((p5 ∨ (False ∧ ((False → p3) → (p5 ∨ ((False ∨ True) → ((((p3 ∨ (p1 ∨ True)) ∨ False) ∨ (p1 → True)) ∨ p4)))))) ∨ ((p3 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40936319874391688073998576126 : ((((((((p2 → (p1 ∨ p2)) ∨ p2) → (p5 ∨ p1)) ∨ ((((p4 → False) ∨ p1) ∧ p3) → (p1 ∧ p4))) ∨ p2) ∨ (p5 → p5)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263432940233448163488401852882 : (True ∧ ((p5 → (((True → p3) ∧ ((((p1 → (p1 ∨ p4)) ∨ p2) ∨ (p2 ∨ p1)) ∧ p2)) → ((p4 ∧ p4) ∨ p2))) ∨ ((p4 ∧ p2) ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216663607802122597240044750037 : ((((p4 ∨ p4) ∨ p4) ∧ p1) → ((((p1 ∨ ((p2 ∨ True) ∧ (p2 ∧ p3))) ∧ (p2 ∨ p2)) ∧ (p5 ∨ (p3 ∨ (p5 → (p5 ∨ True))))) ∨ p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46784394296397926220627303071 : (((p4 → ((p1 → (False ∧ p3)) ∧ ((((p1 ∨ (p3 ∨ p3)) ∨ (p1 ∧ p2)) → (p2 ∧ ((False → p5) ∧ p3))) ∧ p5))) ∧ (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726261934715198617931569736530 : (((((p1 ∨ False) ∨ p3) ∨ ((p3 ∧ p2) → ((p2 → ((p5 → True) ∨ p1)) ∧ (p5 ∧ ((((p4 → p5) ∨ False) ∨ (p4 → p3)) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137491558404331090882879304072 : ((p5 ∧ ((((p1 → (False ∧ (p4 ∨ ((False → p5) ∨ (p4 → p5))))) → (((p2 ∧ p1) ∨ True) ∨ p5)) → False) → p1)) ∨ (False ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322530157203548907584870250023 : (p5 ∨ ((p3 ∧ (p2 ∧ ((((p2 → p5) ∧ p1) ∧ ((p1 → p3) ∧ (p1 ∨ ((p2 → True) → ((p3 ∨ False) ∨ (p2 ∧ True)))))) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41462161227500203860223422512 : ((((p2 ∧ ((p1 ∨ ((p5 → True) ∨ p5)) → (p2 ∧ (True → p3)))) ∧ ((p1 ∧ p3) ∨ ((((p2 ∨ p4) → p5) ∧ False) → p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135165844067353872972879395564 : (((((((p3 → p4) ∧ p2) → (((p2 ∧ p4) ∨ p5) ∨ False)) ∨ (((p1 → p1) → True) ∧ p1)) ∧ p5) → (p1 ∨ p3)) ∨ (p3 → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51445930654965197604880540911 : (((((((p2 ∨ p1) ∨ p3) ∧ (p5 → False)) ∧ (True → (False ∧ False))) ∧ ((p3 ∧ False) → p2)) → (((p5 ∧ (p2 → p3)) → False) → p5)) ∨ p3) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h20 := h6 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124034032437159324644702069088 : (((((p2 ∨ p3) ∧ ((p4 ∧ ((p5 ∨ p2) → p5)) ∧ p2)) ∨ p1) → (((p1 → p4) ∨ True) → (p5 ∧ (p2 ∧ (False ∧ True))))) → (p1 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 ∨ p3) ∧ ((p4 ∧ ((p5 ∨ p2) → p5)) ∧ p2)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48379888475673000398251082354 : (((True → ((((True ∨ (p3 → (p1 → ((p4 ∨ True) → p3)))) ∧ (False ∨ p1)) ∧ (p1 ∧ False)) ∧ ((p5 ∨ p1) ∧ p3))) → (True ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120738291365460435532655100912 : ((((((p3 → p5) ∨ p4) → (((p4 → (p3 ∧ p1)) → ((p4 ∧ p1) ∧ ((p4 ∨ p5) ∨ p1))) ∨ True)) → (p2 ∧ p3)) ∨ False) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119339490968186027283490570237 : ((p3 → (((True ∧ False) ∨ p1) ∧ ((((p1 ∨ p2) ∧ ((p3 → p1) ∨ ((False ∧ p4) ∨ (p3 ∧ (False → p4))))) ∧ False) ∧ p5))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160468904136981634258266284005 : ((((False ∨ p5) ∨ (p4 ∨ ((p5 ∨ True) ∨ (p2 ∨ ((p5 → False) ∨ p5))))) → ((False ∧ p4) ∧ p4)) → ((p1 ∨ p4) ∧ ((False → p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ p5) ∨ (p4 ∨ ((p5 ∨ True) ∨ (p2 ∨ ((p5 → False) ∨ p5))))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428871624132417951609699740151 : ((((((((p4 ∧ ((False ∨ (p4 → p3)) → p5)) ∨ p4) → (True → False)) ∨ ((False ∨ p5) ∧ (p2 ∧ True))) ∨ (p4 → True)) ∨ (p4 ∧ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341160764859634293889222471997 : (p2 → ((((((p4 ∨ ((((p4 ∨ True) → False) ∧ (p5 ∨ p5)) ∨ (False ∨ ((True ∨ p3) ∨ (True ∨ True))))) ∨ True) ∨ p1) → False) ∨ p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 ∨ ((((p4 ∨ True) → False) ∧ (p5 ∨ p5)) ∨ (False ∨ ((True ∨ p3) ∨ (True ∨ True))))) ∨ True) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94797931793144037349607271018 : ((p3 ∧ (((p3 → p2) ∧ True) ∧ ((((p2 ∧ (p5 → (False ∧ p1))) ∧ (((p3 → (True → p5)) ∧ p4) → p1)) ∧ (True ∨ p2)) ∧ p5))) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h16 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h21 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h22 := h15 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66795644687142401440978731513 : ((True → (p2 ∨ (((p1 ∨ True) → (p5 ∧ (p4 → (((p2 → ((p4 → (True ∨ False)) ∧ ((p2 → p4) ∨ p5))) ∨ True) → p1)))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53422366707538062546180730903 : (((((p3 ∧ (p3 ∧ (p2 ∨ p3))) → True) → ((True ∧ False) ∧ p1)) → (((((p4 ∧ (p3 ∧ p5)) ∧ False) → p1) → False) ∨ (p3 ∧ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p3 ∧ (p2 ∨ p3))) → True) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607539980578896396594913781991 : (((((False ∧ (((((p2 ∨ p5) ∨ p2) → False) ∨ (p5 → (p4 ∨ (((p3 ∨ True) → p4) → p5)))) → ((p1 → False) ∧ False))) ∧ p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_698129106864721175853661166505 : (((((((((p1 ∨ (p5 ∨ False)) ∨ p5) → p3) ∨ p2) ∧ p1) → p5) ∨ ((((p5 → (p1 → p2)) → p2) ∨ (False → (False ∧ True))) ∨ p2)) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48145344513588390748717307774 : (((((p1 → p5) ∧ p5) → ((((p5 ∧ ((p5 ∧ p5) ∨ p1)) ∧ True) ∧ (((p2 ∧ (p2 → p3)) ∧ p3) ∧ p2)) ∨ p4)) → (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2095632642928336496427222487 : ((p2 ∧ (p1 → ((p5 ∧ False) ∧ (((p2 ∨ (p5 → (p2 → (p5 ∧ False)))) ∨ p2) ∨ p2)))) ∨ (True ∨ ((p4 ∧ p5) ∧ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168704528421994162649038722504 : ((True ∨ ((True ∨ ((p3 ∧ (p3 ∨ (p2 ∨ p4))) ∨ ((False ∧ (False ∧ p4)) ∧ p4))) → True)) → ((p1 → p3) ∨ (p3 ∨ ((p5 → True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755342293143240543484766257186 : (((p1 ∧ ((((p3 → (False ∨ False)) ∨ (False → ((((p2 ∧ (((p5 ∧ p3) → p2) ∧ (p2 ∧ False))) → True) → p2) ∨ p1))) → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134251311215037422879200664068 : ((((p2 ∨ (False ∨ True)) ∧ ((p5 → ((p3 ∧ p4) ∧ True)) ∧ (((p5 ∧ p1) ∧ (p5 ∨ (False → p4))) ∨ p3))) ∨ True) ∨ (p4 ∧ (p3 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42831719454654926991895721599 : (((p1 → (p4 ∧ (((p3 ∧ p4) → ((((p3 ∨ p1) → p3) → (True ∨ (p3 → ((p2 → p5) ∨ True)))) → (p1 ∧ True))) → p2))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750225901596183972654328606875 : (((True ∧ ((p4 → (p4 ∧ (p3 → (((p5 → ((p3 ∨ p4) ∨ (True ∨ (False ∨ ((p3 ∨ True) ∨ p3))))) ∧ p5) ∨ p5)))) ∧ (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46447551929015888763603313690 : ((((((p2 ∧ p2) ∧ p5) ∧ p1) ∨ ((((p4 → (p1 ∨ p5)) → True) ∨ (p2 → False)) ∨ (False → (p4 ∨ (True → p1))))) ∧ (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67767275447483526327220882333 : ((p2 → (((p5 → (((True ∧ p3) ∧ (p2 → p4)) ∧ p3)) → (((p2 ∨ (p5 → True)) ∧ (((p3 ∧ p1) ∧ False) ∨ p3)) ∨ True)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626141601454198862258410714509 : ((((p3 → ((p4 ∨ ((((((p3 → p3) ∨ (False ∨ p1)) ∧ (p5 ∧ False)) ∨ (False ∨ (p3 ∨ p5))) ∧ p4) ∧ (p4 ∧ p5))) ∧ p1)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706168118132075256067207095550 : (((((p5 → False) → (((p2 ∨ p1) → False) ∨ False)) ∧ (((((p5 ∧ p3) → p5) ∧ ((p1 → p5) ∧ False)) → (False ∨ p2)) → (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324959586196634208720657897896 : (p5 ∨ ((p5 ∨ p3) ∨ ((p2 ∨ (p5 ∧ (p2 ∧ p4))) → ((p1 ∨ False) ∨ (p2 → (((p1 → True) ∨ p3) → (False → (p4 ∨ (p3 ∧ True))))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260308411854733948246303338278 : ((p2 → p4) → ((((p2 → p3) → (False ∧ p5)) ∧ True) ∨ (((False ∨ p1) → ((False → (False → (p5 → (p4 ∧ (p3 ∧ p2))))) ∨ True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668057019711999191745821179151 : ((((p5 ∨ (True ∧ ((p2 ∨ ((p1 ∧ (((p5 ∨ (p5 → True)) ∧ p2) → p1)) ∨ (False ∧ (p5 → True)))) ∨ p5))) ∧ ((False ∧ p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178972113349142442855224371316 : (((p5 ∨ p1) ∨ ((False ∧ p2) ∧ ((p5 ∧ ((p5 ∨ p1) ∨ False)) ∧ False))) ∨ ((p3 ∨ p3) → (True ∨ ((False ∨ ((False ∧ True) → p2)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



