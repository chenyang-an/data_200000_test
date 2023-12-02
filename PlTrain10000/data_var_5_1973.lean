variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200003116003261574988754427474 : ((((False ∧ (p1 → False)) → p3) → (p5 → True)) → ((p2 → (p1 ∧ ((True ∨ p3) → (p1 → p5)))) ∨ ((p3 → (False → (p5 ∧ p4))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114864427759215314111868580448 : (((((p2 ∧ (((True → p2) ∨ p3) ∨ p5)) ∧ p1) ∨ ((p3 ∨ p3) → True)) ∨ (True ∨ (p5 ∧ (p5 ∧ ((p2 → p5) ∨ p4))))) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260489636217018775054644111193 : ((p3 → False) → (((p2 ∨ ((p3 ∨ (p2 ∧ False)) ∨ False)) ∧ p3) → ((p2 ∨ ((p2 → p3) → (((p1 → (p5 ∨ p1)) → p2) ∨ p2))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307884483216467675249972256121 : (p1 ∨ (p5 → ((p3 ∨ True) → (((((((False → p2) → (p2 ∧ True)) ∨ p3) ∧ (((p2 → p1) ∨ p3) ∨ (True ∧ p4))) → True) → p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_62561882715339855670387632165 : ((p3 ∧ (p5 ∨ (((p5 ∧ (((True ∨ p3) ∧ p5) ∨ p2)) → (p3 ∨ (p4 ∧ ((p4 → p3) ∨ (False ∧ ((p2 → True) ∧ False)))))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247764433101707085948284025852 : ((p1 ∨ False) ∨ (p5 → (p3 ∨ (p2 ∨ (True → (((((p4 ∨ (p3 → (p4 → p5))) ∨ (p3 → p1)) ∧ (p4 → p4)) ∧ True) ∨ (False ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234361223475116439922350668876 : ((p1 → (p2 ∨ p5)) → (p2 → (((True ∧ p3) ∨ ((((((p3 → ((p1 ∨ p1) ∨ p1)) ∧ True) → p3) ∧ (True → p5)) ∨ True) ∨ p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749602818563348274324334173856 : (((True ∧ ((((((False ∧ p4) ∨ p2) ∨ ((((p5 ∧ (((True → p3) ∧ p3) → p4)) ∧ False) ∨ p4) → (p4 ∨ p5))) ∨ p5) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192158620206630618153873842986 : ((((((False ∨ True) → True) ∨ (p5 → False)) ∧ p5) ∧ p5) → (((((True ∨ (p3 → True)) ∧ (((p1 → p2) → p1) → True)) → False) ∨ True) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165118221363402556995516136607 : (((p4 → (p2 ∧ ((p3 ∧ p3) ∨ (p2 ∧ ((p3 ∧ ((False ∨ p5) → p2)) ∨ p1))))) → p4) ∨ (p2 → ((p4 ∧ p5) → (p1 ∨ (p4 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7882882829728039272367435018 : ((((p5 ∧ ((p2 ∧ ((True ∨ False) → p3)) ∨ (False ∨ (((False ∧ ((p5 ∨ p1) ∨ p2)) ∨ True) ∨ ((p1 → p2) ∧ p5))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300867057414432312731792837444 : (False ∨ (((((p4 ∨ ((True → (p4 → p2)) → p4)) ∧ (p1 ∨ p3)) ∨ True) ∨ p3) ∨ ((p1 → (True ∨ (True ∧ ((p1 ∧ p1) → True)))) ∧ p2))) := by
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
theorem thm_5_vars_340775521686208573664024066829 : (p2 → ((((((True ∧ p1) ∧ (p4 ∨ ((p3 ∨ (p5 ∨ ((p5 ∨ ((p3 → (p1 ∨ False)) ∧ p5)) → p4))) ∨ p3))) → p5) → True) → False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184892335534122206619979505727 : (((p2 → (p4 ∨ False)) ∧ ((False ∧ (p5 → p3)) ∨ (p2 ∨ p1))) ∨ ((p1 ∧ p2) → (p2 ∨ (True → (((p5 → False) → False) ∧ (p3 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130477751479738370546655683393 : (((p2 → (False ∨ ((p2 ∨ False) → (((((p5 ∧ (p3 ∧ False)) ∨ p3) ∧ p2) ∨ True) ∧ p2)))) ∨ (p3 ∧ (p3 ∧ p3))) ∧ (p1 → (p5 → p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231655998244485735682500487721 : (((False ∧ p4) → p5) → ((((p4 → (True → False)) ∧ (p4 → p4)) ∧ (((True ∧ ((p3 ∧ (p1 → p5)) ∧ True)) ∧ True) ∨ p3)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_844510713310402522836617927447 : (((((((p2 ∨ False) → p1) ∧ True) ∧ (True → (((p3 ∨ (((False ∧ p4) → p3) ∧ p5)) ∧ (p2 ∧ (p4 ∧ p3))) ∧ (False → p4)))) ∨ False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137247864961145363190334425331 : ((p1 ∧ ((p3 ∨ ((False ∨ True) → (True → (p1 ∨ p5)))) → ((p1 ∧ ((p1 → (p4 → p4)) ∧ p4)) ∨ (p4 → False)))) ∨ ((False → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43634428549835470400859589336 : (((((((p3 → (((p4 ∧ ((p4 ∧ ((p5 → p5) → (p5 → p5))) ∧ p1)) ∧ p1) ∨ p1)) ∨ p2) → p5) ∨ (p2 ∧ p4)) → p5) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185390737228230022101539109626 : ((p5 ∧ (p2 ∨ ((True → ((p2 ∨ p2) ∧ True)) ∧ (False ∨ True)))) ∨ (p5 → (((p1 → ((False ∨ (True ∨ p2)) ∨ p3)) ∨ (True ∧ p4)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622950969398785793358396621027 : ((((p5 ∧ ((p1 ∨ (((p4 ∨ (p1 ∨ p4)) ∧ False) ∧ (p2 ∧ p5))) ∨ (True ∧ (p1 → (((True ∧ (p2 ∧ p2)) → p5) ∧ p3))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64669621777822976844290035570 : ((p1 ∨ (p2 ∨ ((p3 ∧ ((p3 → False) ∧ ((False ∨ ((((True → p4) ∨ (p3 → (p1 ∨ False))) ∨ p3) ∧ (True → True))) → p2))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202871211356447642485928110074 : (((False ∧ p5) ∨ (p4 → (True ∨ p3))) ∧ ((False ∧ ((((True ∧ (p1 ∧ (p5 ∧ p2))) ∨ (p3 ∧ p2)) → p5) → p2)) ∨ (False → (p4 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64719189737109269363146591250 : ((p1 ∨ (p3 → (p4 ∨ ((p2 ∨ ((p4 ∧ p2) ∧ p1)) → (p5 → (((((True ∨ p3) ∧ False) ∧ p4) → p5) → ((p1 ∨ True) ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262240913071560625891959794986 : (True ∧ ((((((True ∨ (p3 ∧ False)) → ((True → p1) ∧ ((p1 ∧ p5) ∧ (p3 ∧ p1)))) → p3) ∧ (False → (p2 ∨ True))) → (p2 ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356112890648021600454142708096 : (p5 → ((((p1 → ((((p2 → p1) ∧ p5) ∨ (True → p5)) ∨ (p5 ∧ p3))) → p1) ∨ (False → True)) ∧ (False ∨ (p5 ∨ (False → (p3 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301149793855957554836645154111 : (False ∨ ((((p2 ∧ p1) ∨ False) ∨ (p1 → (p3 ∨ p1))) ∨ ((p3 ∧ p1) ∨ (p5 ∧ ((p4 ∧ (False ∨ False)) → (True ∧ ((p5 ∧ p3) ∧ False))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190044420503087293008280730868 : (((((False → p3) ∧ (False → (p4 ∧ p2))) ∨ p2) ∧ p2) ∨ ((((p3 ∧ p1) ∨ p2) → (True ∧ ((p1 → p1) ∧ False))) ∨ ((p1 ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264610624856656696180532641095 : (True ∧ (((False ∧ False) ∨ p2) → (((((True ∨ (p1 ∧ False)) → False) → ((False ∧ p1) ∨ ((p4 ∨ p2) ∧ p1))) ∧ (p1 ∨ p2)) ∨ (p5 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ (p1 ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342164436662062376019182545335 : (p2 → ((((p3 → (p3 ∧ p1)) → p4) ∨ ((p1 ∧ (p4 ∨ p4)) ∧ ((p4 ∨ (p1 ∨ (p1 → p4))) → p3))) ∨ (((p3 ∧ True) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137434547918981740174107323351 : ((p4 ∧ ((((((p1 → p3) ∨ (p1 ∨ True)) ∨ False) → (p3 ∧ p2)) ∨ (((p1 ∧ p2) ∨ p4) ∨ p3)) → (p4 ∧ p3))) ∨ (False → (p3 ∧ p2))) := by
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
theorem thm_5_vars_103659628445347686648183084805 : ((((((True → (((p2 → p3) ∨ True) → ((p2 → ((p4 ∨ p1) ∨ p4)) ∨ p3))) → p1) ∧ (p4 ∨ p3)) ∧ (True ∧ p3)) → p1) ∧ (True ∨ p1)) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (True → (((p2 → p3) ∨ True) → ((p2 → ((p4 ∨ p1) ∨ p4)) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h18 : (True → (((p2 → p3) ∨ True) → ((p2 → ((p4 ∨ p1) ∨ p4)) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h23 := h4 h18
    -- One of the premise coincides with the conclusion.
    exact h23
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657637404739837444726089313762 : (((((False ∨ p2) → (True ∧ ((((((p3 ∧ ((False → False) ∧ True)) → True) ∧ (p1 ∨ False)) → (p4 → p5)) → p4) ∨ p5))) ∨ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147692450931211622269059371068 : (((((True ∧ ((True ∨ p2) → (((p2 ∧ p3) → False) ∨ p3))) → p2) ∧ (p5 ∨ ((p5 → p4) ∨ p1))) → p5) ∨ (p4 → ((False ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759445688897572793863036286962 : (((p2 ∧ ((((((True → p5) → ((True ∨ p3) ∨ True)) → ((p1 → (p2 → p4)) ∨ p4)) ∧ p3) → p4) ∧ (((p5 → p2) ∧ p3) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193506667111205510285676741408 : (((p5 ∨ p4) ∨ ((False → (True ∧ (True → p3))) ∨ p2)) → (p4 ∨ ((((p3 → p2) ∨ p4) → (p1 ∧ p4)) ∨ (p5 → ((p4 → True) ∨ False))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111343340610814119127662120025 : (((p3 ∧ (p1 ∧ ((p3 → (((True ∧ False) → p5) ∨ ((p3 → ((True ∨ True) ∨ (p2 ∧ p3))) ∨ p3))) → (p1 ∨ p1)))) ∧ True) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112311232138777745457388573782 : (((p2 → ((((p2 → p3) → p4) ∨ False) ∨ ((p4 ∨ (p3 ∨ ((((True ∨ p3) → p4) ∧ (p3 ∨ p5)) → p1))) ∨ p2))) ∨ p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66555142966294506143447136890 : ((True → (((((p5 → p1) → p5) ∨ (p5 ∨ (p3 ∧ p4))) ∧ ((False ∨ p5) ∨ (((p4 ∨ True) ∨ p2) ∨ (True ∨ p5)))) ∧ (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115399432303612862546865149384 : (((p5 ∧ (((True → (p1 → p2)) ∧ p3) ∧ False)) ∧ ((p2 → ((p3 → False) → (((False ∨ p5) ∨ (p2 ∨ p3)) ∧ p4))) → p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192652543285990756815026233658 : ((((p5 → (((p3 ∧ p5) → False) → p5)) ∨ p4) → False) → (((False ∧ (p1 ∧ p1)) ∨ ((((p4 → True) → p2) ∧ p2) → False)) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (((p3 ∧ p5) → False) → p5)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40976901532386694355365975287 : (((((p1 ∧ p5) ∨ ((((((True ∨ (p2 → (p5 → p4))) → False) ∨ (p3 → p3)) ∨ p1) → (p1 ∧ False)) ∨ p1)) ∨ (False → p1)) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190840512480651053031869818070 : ((((((False → p4) → p2) ∨ p3) ∧ True) → (p2 ∧ p1)) ∨ (p4 → ((False ∧ ((p2 → False) → (p2 ∧ False))) ∨ (((p2 ∧ p5) ∨ p1) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218490511099561889988532391218 : (((p1 ∨ True) → (p4 ∧ False)) → (((True ∧ (False ∧ p5)) ∨ ((((p2 ∧ (False → p1)) ∨ (p2 → p5)) ∧ (p5 ∨ p3)) → (False ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47718313615036438546534230197 : ((((((((p2 → (True ∧ ((((False ∧ p5) → p3) → True) ∨ p5))) ∨ (p4 → p1)) → (p4 ∧ p1)) ∧ True) → True) ∨ p5) → (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62344961184790400171880144873 : ((p3 ∧ ((((p5 ∨ (False ∨ (True → p4))) → (False → (p2 → (((p3 ∨ True) → False) ∨ (True ∧ p2))))) ∨ True) → ((True → p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192738208557702947074491596460 : ((((p4 ∧ p3) ∨ ((p4 ∧ p5) ∨ (True ∧ True))) → p5) → ((p1 ∨ (((p2 ∨ (p1 ∨ ((False ∨ p2) ∧ p1))) → False) ∨ (p2 → p2))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311958675852543917677015850779 : (p2 ∨ (p3 ∨ ((False ∧ p2) ∨ (((((p3 ∨ p4) → True) ∨ False) → False) → ((True → ((p4 ∧ ((False → (p4 ∧ p4)) → p4)) ∧ p5)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ p4) → True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258765464136162147042095334641 : ((True → False) → (((((p5 ∨ p1) ∨ False) ∨ p1) ∨ (((p5 ∨ ((p2 ∧ p2) ∨ ((p4 ∨ p2) ∧ (p1 → p1)))) → (True → p4)) ∧ p5)) ∨ p5)) := by
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
theorem thm_5_vars_57969012013674391784192506426 : (((p3 → (p2 ∧ p3)) → (((p3 ∧ ((p5 → (((p1 → (p1 ∨ p4)) ∨ p4) ∨ ((p4 → (p2 ∨ p1)) ∨ True))) ∨ p3)) ∨ p1) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234206783712198420134035766240 : ((False → (p3 ∧ p2)) → ((p5 → p1) ∨ (((p3 → p3) ∧ (True → ((((True ∨ False) → False) ∨ True) ∨ ((False → (p5 ∨ p3)) ∨ p5)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707447031778319773547082512316 : (((((False ∧ (p4 ∧ p2)) ∧ ((p1 ∨ p4) ∨ p4)) ∨ (True ∨ (((True ∧ False) ∧ p1) ∧ (p4 ∨ (((p3 → (p4 ∨ p2)) ∨ p1) ∧ p3))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_10564161581526852565077292698 : (((p4 → ((p1 ∨ (((p4 → p2) → False) → (((p4 ∧ p3) ∧ (p3 → (p5 ∨ (p2 ∧ (True ∧ (p1 ∨ p2)))))) ∧ p2))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_182221008936967994424914721777 : ((((True → ((False → p5) ∧ (p2 ∧ p2))) ∨ (False ∧ p4)) → p2) ∧ (p1 → ((p2 → ((p5 ∨ ((p2 → True) ∨ p3)) ∧ (False ∧ p3))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318887359784675596026910584843 : (p4 ∨ (((p1 → True) ∧ ((((((False ∧ p1) ∧ (True → (p4 → (True ∧ p3)))) ∧ False) ∨ False) ∧ (p1 ∧ p3)) ∧ p5)) ∨ ((p3 → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313990147755997604931232249840 : (p3 ∨ (((False ∨ (p3 ∨ p4)) ∧ ((((True ∧ p1) ∧ (p5 ∧ (p2 ∨ (False ∨ False)))) ∨ (True ∨ (p2 ∨ p2))) ∧ (p1 ∨ p2))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63938577797382333660568564858 : ((False ∨ (((((p4 → ((p2 → p3) → (p1 ∨ p2))) ∨ False) ∧ (p4 ∨ False)) ∧ (p1 ∧ (True → (((False ∧ p3) ∧ p5) ∨ p4)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593866582992561594841456170070 : ((((((p4 → ((p2 ∧ (((False → (p5 ∧ (False ∧ p2))) → False) ∨ (p4 → True))) → False)) ∨ p3) ∨ (p1 → ((p3 ∧ p1) → p2))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41325502873595576486871038844 : ((((p2 ∨ ((p5 ∨ ((False → p3) → (p4 ∨ p5))) ∧ (((False ∨ p5) ∨ p5) → p1))) ∧ (p2 ∨ ((p4 ∨ (p3 → p2)) ∧ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115317720536210539977983037206 : (((((False → False) → False) ∧ (p2 → (p4 ∨ (p1 → p1)))) → (False ∨ (((((p4 → p4) ∨ True) ∨ p5) ∧ (p4 ∧ p2)) ∧ p3))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135655561512209212610685043796 : ((((p1 ∧ (p1 ∨ True)) ∨ (p1 ∧ (False ∨ ((p2 ∧ (p4 → p4)) → (p2 ∧ p3))))) → ((p3 ∧ (p1 ∧ p1)) ∨ p5)) ∨ (p5 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114972163196717865738747069442 : (((((((p5 ∨ p2) ∨ True) ∨ (p5 → (False ∧ p4))) → p1) ∧ p3) ∧ (False ∧ (((((p1 ∨ p4) → p5) ∧ False) ∨ p4) ∨ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313133662384564013112272254627 : (p3 ∨ (((((p1 ∨ p1) ∧ ((((p4 ∧ False) → False) ∨ False) ∧ (p2 ∧ (p5 ∨ False)))) ∧ False) ∧ (((True → p3) → False) ∨ (True ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46940912313653350783917380072 : ((((False ∨ ((((p1 ∨ p4) → (p2 → (True → (p2 ∨ (p5 → (p5 → (p4 ∨ p2))))))) ∧ p4) ∨ (p3 ∧ p5))) ∨ p2) ∨ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234318147260252622644557105868 : ((p1 → (p2 ∧ p1)) → (((p2 ∨ p4) → ((p2 ∧ ((p4 ∧ ((p1 → p4) ∧ (p4 → False))) ∨ (p2 ∨ p4))) ∨ (p3 ∨ p3))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125102852115922789066767203702 : (((p2 → (p3 ∧ p4)) ∧ (((p4 ∧ True) ∧ p3) ∧ ((p3 ∧ (p3 ∧ p2)) ∧ (True → ((p5 → (True → p1)) → (p5 ∧ p4)))))) → (p1 → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h6.left
  let h12 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h18 := h12 h17
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h19 : (p5 → (True → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h22 := h18 h19
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- One of the premise coincides with the conclusion.
  exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328974588240919552831569789556 : (True → (((((p5 ∧ p3) ∨ p1) ∧ p2) ∧ p3) ∨ ((p1 ∧ p2) → ((False ∨ ((((True → p4) → p5) ∧ p1) ∨ p2)) ∧ ((p1 → p4) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148640320337394518253952571220 : ((((((p2 ∨ True) ∧ (p3 ∧ p4)) ∧ p5) ∨ p4) ∧ (((False → ((p2 ∧ True) ∧ p4)) ∧ p1) ∨ (True ∨ p1))) ∨ ((p3 ∧ (p2 ∧ False)) → False)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351736754269981721837185835347 : (p4 → (((p1 ∨ p5) ∨ ((False ∨ (p1 ∧ (False ∧ p3))) ∨ (p2 ∨ (False ∧ p3)))) ∨ (((p5 ∨ p2) → p3) → (p2 → (p1 ∨ (p2 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349440064421562124402719906118 : (p3 → (p4 → (p2 ∨ ((((p4 ∨ p2) → ((p2 → ((((p1 → (p2 ∨ False)) ∧ p5) → False) ∨ p1)) ∨ p4)) ∨ (p4 → (False ∨ True))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157052002026373788537388810317 : (((p2 ∧ (((True ∨ True) ∨ p5) → (p5 ∧ ((False ∨ ((p1 ∧ p1) → True)) → (p4 ∧ p5))))) ∨ False) ∨ (((p1 ∨ p5) → (p5 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117167672811140907850068433447 : ((True ∧ (((((((p5 ∧ (True → (p3 → True))) ∧ (True ∧ p1)) → (True → False)) → (p2 ∨ (False ∧ True))) → p3) → True) → p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157636874978576799943886234367 : (((p2 ∧ ((False → ((p5 → p4) ∧ (((p3 → p1) ∧ p5) → True))) → p2)) ∧ ((False ∧ p4) ∨ p4)) ∨ ((False ∨ (p3 ∧ (p2 → p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62272182618700995202308668384 : ((p3 ∧ (((p1 → (p1 ∨ ((True ∧ (((False ∨ (((p1 ∧ False) ∧ (p5 → p3)) → p5)) ∧ True) ∧ p4)) → p2))) ∨ (p1 ∨ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40779413375823702409380082492 : ((((p1 ∧ ((True ∧ ((p3 → ((p3 ∨ (((p4 ∨ p1) → p4) ∨ (True → (False ∨ (p3 → False))))) ∧ p4)) ∨ p3)) → p1)) → p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697071540586401128689603884465 : (((((False → (True ∧ (p4 → (True → p1)))) → (p5 ∧ (p4 ∨ p4))) ∧ (p3 ∨ ((((True → (p5 ∧ p1)) ∧ p5) ∧ (p3 → p5)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194260185391622069283452167657 : ((p5 → ((p1 ∧ ((p2 → (p3 ∨ True)) ∧ p4)) ∧ p3)) → (p5 → (p4 ∧ (p5 ∧ (True → (((p4 ∨ p1) ∧ p3) ∨ (p1 → (p3 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696035061851493059695033289983 : ((((p2 ∧ ((False → False) ∨ (((False ∨ ((p4 → p2) ∨ p3)) ∨ p4) ∧ p1))) → (p3 ∧ ((True ∨ (False ∨ (p5 ∨ (True ∧ p2)))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41478670539062056717747775375 : ((((((p1 ∧ p2) ∧ p1) ∧ ((p2 ∨ p2) ∧ ((False ∨ p2) → p2))) ∨ ((True ∧ (((p1 ∨ True) ∨ p3) ∨ (p4 ∨ p3))) ∧ p3)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307253222780059853856413577982 : (p1 ∨ (p2 ∨ ((((p2 → ((((True → p5) → (p2 ∨ p2)) ∨ p1) ∧ p1)) → True) ∧ (((p3 ∧ True) ∧ (p1 ∧ p3)) ∧ True)) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_783150986388539135065746880616 : (((p3 ∨ ((False ∨ (((p4 → p4) ∧ p2) ∧ ((True → (True → p3)) → (((p5 → p3) → p4) ∨ (p5 ∧ p3))))) ∧ (False ∧ (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260910410125935039323627255137 : ((p4 → False) → (((((False → (p2 ∨ (p3 ∨ (False → False)))) → (False → True)) ∨ False) → p3) ∨ (((p1 → p2) ∨ p5) ∨ (p2 → (True ∨ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44047386193886779677419115012 : ((((p5 ∨ (((False ∨ (p1 ∨ (((True → (False → (p5 → ((True ∨ p4) ∧ p1)))) ∨ p1) ∧ p4))) ∨ p2) → p1)) → (True → p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208995430079646378654439537283 : ((False ∨ (((p5 ∨ True) ∧ p2) ∨ p5)) → (((p4 ∨ (p2 ∧ ((p4 ∨ False) → p1))) ∨ ((p4 → (p4 ∨ ((p3 ∧ False) ∧ p1))) → p2)) ∨ True)) := by
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
theorem thm_5_vars_59330778744558059089528950780 : (((p4 ∨ p4) ∨ (((False → p2) ∧ p1) → ((False ∨ p5) → (((p3 ∨ ((False → p1) ∨ p2)) ∧ (False ∧ (p3 → False))) ∨ (True ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620356278818067801154952215136 : (((((p2 ∨ p4) ∨ ((((p5 ∧ (p1 ∨ (p5 ∨ True))) ∧ (p3 ∨ p1)) → ((True ∧ p1) ∧ p3)) ∧ (True ∨ ((p2 → p5) ∨ False)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_208439352214296028047192574760 : (((p5 ∨ p4) ∨ (False → (p4 ∧ p4))) → (((p3 ∧ ((False → p1) ∧ p2)) → (((((p1 ∧ p3) ∧ (True ∨ p3)) ∧ p5) ∧ p2) ∨ True)) ∨ p1)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49940695563941651699889302455 : (((((False ∧ p2) ∧ (((p1 ∨ ((p4 → True) → p2)) → p1) ∨ ((p3 → False) ∧ False))) ∧ (True → p1)) ∧ (p3 → (p1 ∧ (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204242942073706751717679877751 : ((((p2 ∨ False) ∧ (p3 ∧ p3)) ∧ p4) ∨ (p4 → (((p4 ∧ (p1 → p4)) ∧ (p5 ∨ p3)) ∨ ((p4 → p2) → (True → (p4 ∨ (True → p1))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187123771145413947361950824986 : (((True ∨ p3) ∨ (((p3 → p4) ∧ (p1 ∧ (False ∧ True))) ∧ p2)) → (((True ∧ p5) ∧ (p5 ∧ p2)) ∨ (False ∨ ((p1 ∨ True) → (p1 ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
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
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862650888732362376715256102754 : ((((((((p1 ∨ ((((p3 ∨ p3) → p4) ∨ p4) ∧ True)) → p1) ∨ (p3 → p4)) ∨ p1) ∨ (True ∧ (True → ((p2 → p2) ∧ True)))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∨ ((((p3 ∨ p3) → p4) ∨ p4) ∧ True)) → p1) ∨ (p3 → p4)) ∨ p1) ∨ (True ∧ (True → ((p2 → p2) ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777020970262397957200869966803 : (((p1 ∨ ((((p2 → p4) ∧ (((p1 → (p2 ∧ (p4 ∧ (((p2 ∧ p5) → (p3 → p2)) ∨ p2)))) ∧ p1) → p5)) ∨ p4) ∨ (p2 ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_677878562297813209140338044892 : ((((((p1 ∧ ((False → (((((p4 ∨ False) ∨ p4) ∨ p4) → False) → p2)) ∧ p1)) → p5) ∨ (False → p3)) ∨ (True → ((p3 → False) ∧ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_173752160246760737944134475803 : ((((True ∨ (p2 ∨ (p4 ∨ False))) ∧ ((True → p5) ∨ ((False ∨ p5) → False))) ∨ p1) → ((((p4 ∨ (True ∨ (False ∨ p2))) ∧ p2) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118667790658604692637814990840 : ((p4 ∨ (True → ((((p4 ∧ p3) ∧ False) ∨ (((p5 → (p5 ∨ p2)) ∨ p1) ∨ (((True ∨ p3) ∨ (True → p2)) ∧ False))) → p5))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214251629490008939321510387342 : (((p1 ∧ (False ∨ p5)) → p4) ∨ (p2 ∨ ((p4 → ((p2 ∨ p1) ∨ ((True ∧ (((p5 ∧ p2) → False) ∧ ((True → p5) → p1))) ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25414946788983606705060394590 : (((True ∧ (True → p1)) → (((((p5 ∧ ((p1 → (False → p5)) ∧ p2)) ∧ p2) → p5) → False) ∨ (p2 → (p2 ∧ (True → (p5 → p5)))))) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56098793167471441498552700088 : ((((p2 ∨ False) ∧ (p2 ∧ p5)) ∨ (((p4 → (False ∨ (((p2 ∨ False) ∨ (True → ((p2 → True) → p5))) → (p3 → True)))) ∨ False) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_137919925158323668654875588504 : ((p4 ∨ ((p4 → p1) ∨ (((False ∨ (p5 → True)) → ((False ∧ p5) ∨ p5)) ∨ (p5 ∨ ((True → (p2 ∧ False)) → p2))))) ∨ ((True ∨ False) ∧ True)) := by
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
theorem thm_5_vars_319783117044041155273175601346 : (p4 ∨ ((((p4 ∨ False) ∨ True) → (p4 ∧ p2)) → ((True → p5) ∨ ((p5 ∨ ((((p2 ∨ (p5 → (p2 ∧ p4))) ∧ p4) ∨ False) ∧ p1)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



