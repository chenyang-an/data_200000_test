variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50257438826879452524907379569 : ((((p2 ∨ (((p4 → ((((p1 ∨ p5) ∨ p4) ∧ ((False ∨ p1) ∧ p3)) ∨ p3)) ∨ True) ∧ True)) → p2) ∨ ((True → (p5 ∧ p5)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37958647431436765367273213575 : ((((((((p5 → (p4 ∧ True)) ∨ (p4 ∨ (True → p4))) ∧ (p1 ∧ (((p1 → p1) → p1) → True))) → p2) ∨ False) ∨ (p1 → True)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16617121637920180488910777734 : ((((((((p5 ∧ p5) → False) → p2) ∧ (True ∧ ((False ∨ p3) ∧ True))) ∨ ((p1 ∧ (p1 ∧ p1)) ∧ True)) ∨ p4) ∨ (False → (p4 ∧ p5))) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198687242792881131793470893794 : ((p4 ∨ ((p5 → p2) → ((p5 ∧ p1) ∨ False))) ∨ ((False ∧ p2) → ((p1 → ((True → p3) ∧ p5)) ∨ (p2 → ((p3 ∨ (p2 → p3)) ∧ True))))) := by
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
theorem thm_5_vars_781945641510766335381991480814 : (((p2 ∨ (p3 → ((True → ((((p2 ∨ p5) ∨ False) ∨ (p4 ∨ ((p5 ∧ False) → (p5 ∨ p1)))) ∧ (((True ∨ p5) ∧ True) ∧ p3))) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186638663341121976065283423851 : (((p5 ∨ (False → (True ∨ (False ∧ (p5 ∧ p4))))) → (True → p4)) → (((p4 ∨ p1) ∨ (((p2 ∧ True) → True) → ((p2 ∧ p1) ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49177249487172971856037729138 : ((((p2 ∨ ((p2 → p3) ∨ True)) ∧ (((p4 ∨ (p5 ∧ (((p3 ∨ p1) → p4) ∨ p2))) ∧ (True ∧ p1)) ∨ p5)) ∨ (p5 ∨ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215915109834184114522455685353 : ((p3 ∨ (p1 ∧ (p2 ∨ p5))) ∨ (p2 → (False ∨ (((((True → (p5 ∨ False)) ∧ (False → ((p5 ∨ p4) ∨ p1))) ∨ True) → (p5 ∨ p2)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324717037789752930984439281027 : (p5 ∨ (((True → False) ∨ False) → ((p1 → ((False ∨ ((p2 ∧ ((p4 ∧ p3) → p5)) ∧ p5)) ∨ ((p4 ∧ ((p3 ∧ True) → p3)) ∨ p2))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157790486757444932568979519106 : ((((p4 → (p4 ∧ False)) → (p2 ∧ (p3 ∨ ((p2 ∧ True) ∧ p3)))) ∨ (p4 ∧ (True → (p4 ∧ p1)))) ∨ (((False ∧ p5) ∧ True) → (p5 ∧ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259424122026153155688762686278 : ((False → p3) → (p5 → (((False ∨ (p1 ∨ ((p2 ∧ p3) ∨ p2))) → (((p1 → p5) → (p2 ∧ (p5 ∨ False))) ∨ True)) ∧ (False → (p2 ∧ p2))))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321744090679804097570248115669 : (p4 ∨ (p5 → (((p1 ∨ ((p3 ∨ True) → p1)) ∧ False) ∨ (p4 ∨ ((((False ∧ p3) ∨ True) ∧ p2) ∨ (p4 → ((p4 → (True ∨ False)) ∨ p4))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184501810607329212218959069129 : ((((p2 ∧ p2) ∧ (True ∧ ((p3 ∨ p4) → p2))) ∨ (p3 ∧ False)) ∨ (((p2 → (((p5 ∧ ((True → p2) ∧ p3)) → True) ∧ False)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306436661015433806778101454940 : (p1 ∨ ((False ∨ False) ∨ ((p1 → ((False ∨ (p5 ∨ p2)) ∨ ((p1 ∨ (p2 ∨ (p1 → ((True ∨ (p3 ∨ p4)) → p1)))) → p5))) ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_685892236461395411880108784520 : (((((p3 ∨ ((p4 → (True ∨ (p1 → (((p4 → True) ∧ p3) ∧ True)))) ∧ (False ∧ False))) → False) → ((p4 ∨ ((p1 ∧ False) ∨ p4)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721728888809999182473107564804 : ((((p1 ∨ ((p1 ∧ p2) ∨ p1)) → (((p2 ∨ ((p5 → p3) → p2)) ∨ (p2 ∨ ((p2 ∧ ((False ∧ (p2 ∨ True)) ∨ False)) ∨ False))) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157662661864720458135409038932 : ((((p2 ∨ ((p2 → p1) → (p2 ∨ (p4 ∧ (p3 → p5))))) ∧ (p5 ∧ True)) ∨ (p5 ∨ (True ∨ p3))) ∨ (p5 ∨ ((True ∨ (True ∧ p5)) → p3))) := by
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
theorem thm_5_vars_47580756993717963845361043193 : (((p1 → (p2 ∨ (((True ∨ p3) ∧ p5) → (((p5 ∧ True) → (p3 → True)) ∧ (True → (((p2 ∧ False) → p1) → p4)))))) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262407483047659282028849889583 : (True ∧ ((True ∧ ((p2 → True) ∧ ((p4 ∨ ((p3 ∧ (p3 ∧ p2)) ∨ (p5 → (False → True)))) → (((p3 ∨ p2) ∨ (True → p2)) ∨ True)))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803297254694164885873141038682 : (((p3 → ((((p5 ∨ ((p2 ∨ ((p1 ∨ p4) ∨ p3)) ∨ p3)) ∧ p4) ∧ (((p5 ∧ p5) ∨ p3) → (((p5 ∨ p5) ∨ p4) ∨ p4))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46876200178842915500872950965 : ((((p5 → (((((p5 ∨ p1) → (p2 → (False ∨ (False ∨ p2)))) ∨ (True → True)) ∧ (p2 ∧ p5)) ∧ (p2 → p1))) ∧ p1) ∨ (True ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622325144258964409094970685064 : ((((p3 ∧ ((((((p2 ∨ False) ∧ p1) ∨ p5) ∧ (p2 → (p1 → p2))) ∧ (((True → p3) → (True ∨ (p5 ∨ True))) → p1)) → False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317776371629549961348074499960 : (p4 ∨ (((p2 ∨ ((((p4 → p1) ∨ (True → (p2 → p2))) ∧ p4) ∨ (p5 ∨ p2))) → ((False ∧ (p4 → ((p1 ∨ p5) ∧ True))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64621612986921543005004798498 : ((p1 ∨ (False ∧ ((p5 ∨ (True ∨ ((p1 ∧ p3) ∧ (p5 ∨ p1)))) → ((((p3 ∨ False) ∨ False) ∧ (((True ∨ p3) → True) ∧ p2)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181227392598972536061995403211 : ((p3 ∧ ((((p2 → p3) ∨ p3) ∨ ((p2 → True) ∨ (True → False))) ∨ p5)) → ((p2 ∧ (p3 ∨ (p3 → False))) ∨ ((False ∨ (True ∧ p3)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
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
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213161376238098216717540714302 : ((((p3 ∧ p2) ∨ p3) ∧ False) ∨ (p1 ∨ (((((False → (p3 ∨ True)) ∨ p3) ∧ p4) → (p1 → (p4 ∨ p2))) ∨ ((p1 ∧ p5) ∨ (p3 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862717573021267136725936410551 : ((((((((True → (p3 ∨ p4)) ∨ True) ∨ p3) → (((p3 ∨ (p2 → False)) ∧ True) ∨ False)) ∨ ((True → (p5 ∧ (p5 → p4))) → p5)) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True → (p3 ∨ p4)) ∨ True) ∨ p3) → (((p3 ∨ (p2 → False)) ∧ True) ∨ False)) ∨ ((True → (p5 ∧ (p5 → p4))) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244947774705144693545376164280 : ((p1 ∧ p3) ∨ (((p3 ∧ p4) ∨ False) ∨ ((p3 → p4) ∨ (((True ∨ (p5 ∨ p2)) ∨ True) → (p1 ∨ ((False ∧ ((p5 ∧ p3) ∨ p3)) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65626784859133671154756808395 : ((p4 ∨ ((((p5 ∧ False) ∨ ((((((p1 ∨ p1) ∨ (p3 ∨ (True → p1))) ∨ p5) ∨ p1) ∧ p4) → (p5 ∨ (p1 → p1)))) ∨ True) ∨ False)) ∨ p4) := by
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
theorem thm_5_vars_149208824572490125647146869741 : (((True ∧ p5) ∨ (True ∧ (((p1 → p3) ∧ (p3 ∧ p2)) ∧ (((((p4 ∧ p4) ∨ False) ∧ True) ∧ True) ∧ True)))) ∨ (p1 ∨ (True ∧ (False → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311927257451414114851069567077 : (p2 ∨ (p3 ∨ (((p3 ∧ p1) ∨ (((p4 → (True → p1)) ∨ p4) ∨ (p2 → (True → (False → (p1 ∨ (p1 ∧ ((p2 ∧ p5) ∨ p3)))))))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186557261049979145600905522049 : (((True ∧ (((True ∨ p3) ∧ (p3 → p4)) ∨ p4)) ∨ (p2 → p3)) → ((p4 ∨ (p5 ∧ p3)) → ((((p1 ∧ (p1 ∨ p4)) ∨ p3) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
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
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209187189109557495498584612401 : ((p4 ∨ ((p1 → (p3 ∧ p5)) ∨ p1)) → ((True ∧ False) ∨ (p2 → (p5 → (((p4 ∨ p4) → p2) → ((p4 ∧ p4) → ((p5 ∧ p3) ∨ p4))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165179968263129769953455454757 : (((p3 ∨ (((p5 → p5) ∧ (p5 → p1)) → (p2 ∧ (p4 ∧ (p4 → p5))))) ∧ (False ∨ p5)) ∨ (p3 → (True ∨ (False → ((p1 ∧ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638455710225849049240457909501 : (((((((p1 → p1) ∧ (p5 ∨ True)) ∧ p2) ∨ (((True ∨ ((p4 ∧ ((p3 ∧ p4) → (p5 ∨ False))) ∧ (p4 → p5))) ∧ p1) → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166710433566689157756657038615 : ((p3 → (((p5 ∧ (((True → p1) ∨ (p4 ∧ p5)) ∨ p1)) ∨ True) ∧ ((True ∧ p1) ∧ p3))) ∨ ((p1 ∧ (True ∧ ((p4 ∨ p2) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677668386065958472950505233472 : (((((((p2 ∧ p3) → (False ∧ ((p4 → p5) ∨ ((False ∧ p1) ∨ p4)))) ∨ (False → (p5 ∧ True))) → p1) ∨ ((True → True) → (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42823103472342258294343141832 : (((p1 → ((False ∨ ((p5 ∨ True) ∧ p2)) ∧ (((((p1 → p5) → False) ∧ p2) → ((True → (p5 → False)) ∧ (p3 → p1))) ∧ p5))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320513844672150968375349992427 : (p4 ∨ (True ∧ (((p4 ∧ p2) ∨ ((p4 → ((p4 ∧ False) ∧ p4)) → (p5 → (((p2 ∧ p1) ∧ (p1 → (True ∧ False))) → False)))) ∧ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112823063377962502698032703774 : ((((p4 → ((False ∧ p2) ∨ True)) ∧ ((((p1 ∧ ((p5 ∧ ((False ∨ p2) → p1)) → (p2 ∧ p3))) → False) ∧ False) → p2)) → p3) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810064695627281167855137461168 : (((p5 → (((((p4 ∨ (p1 ∧ False)) → ((((p5 ∧ p2) ∨ p5) → p3) → (True ∨ p5))) ∧ True) → p2) ∨ ((False ∧ (False → p4)) → False))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56421480813207232279115368075 : ((((p4 ∧ p5) ∧ (p1 → p5)) → ((((p4 → (p4 ∨ p2)) ∨ False) → (p1 ∧ (p1 → ((p4 ∨ (p3 ∨ (True ∧ p5))) ∨ True)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119440443087934289639474332634 : ((p4 → ((p4 ∧ (p3 ∨ ((p3 ∨ (False ∧ ((p3 ∨ (p1 → True)) → p1))) ∨ p1))) ∨ ((p3 ∧ (p3 ∧ True)) → (p4 ∨ p5)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44932068342151743250987029597 : ((((p3 ∧ p3) ∧ ((True ∧ ((True ∨ p4) ∨ ((((((p5 ∧ p3) → (p1 ∨ (False → p3))) ∧ p5) ∨ p4) → p2) → p4))) → True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962585021285616063931716417997 : ((((True → p4) ∧ (False → (False ∧ ((True → False) → ((True → (p3 ∧ p1)) → (True → ((p1 ∧ (True ∨ ((p3 ∨ False) → p2))) ∨ p3))))))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593425248100167223747354668845 : (((((((((p2 ∨ (p1 ∨ (p1 ∧ (p4 ∨ True)))) → True) ∧ (p5 ∧ p5)) → p3) → ((True ∨ True) ∧ p4)) → (p2 ∧ (p5 ∧ p3))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47490372931814508152834728916 : (((False ∨ ((p2 → p4) ∧ ((p2 → ((p3 ∨ (((p3 ∧ (True ∨ True)) → p5) ∧ False)) ∧ (False ∧ p1))) → (p5 → False)))) ∨ (p5 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694258721046626064923538078631 : (((((p3 ∧ (p3 ∨ (p4 ∨ p5))) → ((p1 ∨ (p2 ∨ p1)) ∧ (p5 → p4))) ∨ (p4 ∨ (False → (p5 ∧ ((p1 → (True ∨ p3)) ∨ p3))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179337781258283325268859727391 : ((p1 ∨ ((p1 ∧ (p5 → True)) ∨ ((p5 ∨ p1) ∧ ((True ∨ False) ∨ False)))) ∨ ((p5 ∨ True) ∨ (((True ∨ True) ∨ (p3 ∧ p3)) ∨ (False ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671541776466087998401356618941 : ((((p4 → ((((p5 → p5) ∧ (((p2 ∧ ((False ∧ True) → p5)) ∨ False) → True)) → (p3 ∨ False)) ∨ (True → p5))) ∨ ((p3 ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136436816873721325634598564548 : ((((False ∨ p4) ∨ (True → True)) → (((p1 → p1) ∧ ((p5 ∧ p3) ∧ p3)) ∨ ((True → ((p1 ∨ False) → p4)) ∨ p4))) ∨ ((p4 → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133840561255986986946651096798 : ((((p3 → p2) → ((True ∧ (((False ∧ p1) ∨ p5) → p1)) → ((p4 ∧ (((False ∧ p1) → p2) ∨ True)) → p3))) ∧ False) ∨ (p2 → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139684555601599128296542549854 : (((((p1 ∨ True) ∨ p3) → ((((((p4 ∧ True) → p2) → p5) → ((p2 ∧ p1) ∧ p3)) ∨ (p5 ∨ False)) ∨ p4)) → p4) → (p5 → (p2 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41885923176095716985437603608 : ((((p3 ∨ (p2 ∨ p3)) ∨ ((p5 ∨ (False ∨ p3)) ∧ (True ∨ (p1 → (False ∧ (True ∨ ((p4 → (p4 ∧ (False ∧ False))) ∧ p4))))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260038336154699859708470047862 : ((p2 → False) → ((((True ∧ ((p4 → p3) → (p3 ∧ ((True ∧ p2) → p1)))) → (((p3 ∧ p2) ∨ (p2 → (True ∧ p2))) ∧ True)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168582232806109901290981355007 : ((p2 ∧ ((((p1 ∧ p4) ∨ (p4 ∨ p2)) ∧ p1) → ((p3 → (False → p3)) ∨ (False → True)))) → ((p2 ∧ (p5 → p1)) ∨ ((p3 ∧ p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63930826337418303887088146563 : ((False ∨ (((p4 ∨ (p1 ∧ ((p5 ∧ ((p5 ∧ p2) ∨ p2)) ∨ ((((p1 ∧ True) → (p3 ∨ True)) ∧ False) → (p1 → True))))) → False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39630742082550223615367204988 : (((p3 ∨ ((True ∧ (p4 → (False ∧ ((((p1 ∨ False) ∨ True) ∧ ((p1 ∨ (p3 → p4)) ∧ False)) ∨ (p5 → (p4 ∨ p1)))))) ∧ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158453387654104575773990453538 : (((True → False) ∨ ((((((p1 → (((False ∨ False) ∧ p2) ∨ p3)) → p2) → False) → p2) → False) → p5)) ∨ ((((False ∧ p2) → p3) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p2) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353556379547600372995638211756 : (p4 → (p3 ∨ ((p1 ∧ ((p3 ∨ p3) → ((p1 → (False → True)) → p2))) ∨ (p3 → ((p5 → (((p5 ∨ True) ∨ p5) ∨ (p4 ∨ False))) ∨ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225161576990423265748151057592 : (((p3 ∧ p4) ∧ p5) ∨ ((p1 ∧ False) ∨ ((p5 → ((False → (p2 ∨ p4)) ∨ p4)) ∧ (True ∨ (((p1 ∨ (False → True)) ∨ (p2 ∨ p2)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152428102532281340393222045491 : ((((p2 → p3) ∧ p1) ∧ (p3 ∨ ((((p3 → p4) ∨ p2) ∧ (((p2 → p2) → True) ∧ p1)) → (False → p5)))) → ((p5 ∨ (p2 → p2)) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745960686350814952045607572399 : ((((False ∨ p4) → (((p1 ∨ True) → (p3 → p4)) ∧ (((p1 ∨ (((((False ∧ p3) ∨ p2) → True) ∨ p4) → (True → p5))) ∧ p1) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118636647881487303583677617683 : ((p4 ∨ ((p3 ∧ False) ∧ (True ∧ (((p4 → ((True → p5) → p2)) ∧ (((p2 ∧ True) ∨ p1) → ((p5 → True) ∧ True))) ∧ p4)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143329273271967818630648496016 : ((p4 → ((p2 ∨ (((p4 ∧ (p4 → p1)) → p1) → (p1 ∨ False))) ∨ (p5 → ((False ∨ (True ∧ (p2 ∨ p3))) → p4)))) → ((p1 ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118337508817163362577911160678 : ((p2 ∨ (((((((p1 ∧ (((True ∨ p4) → p3) ∨ p1)) ∧ True) ∧ True) ∨ ((p4 ∧ p2) ∨ (True → p4))) → False) → p3) ∨ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166313576505243913528253457252 : ((p5 ∧ (((p3 ∨ True) ∧ (((p1 ∨ (p4 → p2)) → (True ∨ (p5 ∨ p1))) ∧ p4)) ∨ p3)) ∨ (p5 ∨ ((p1 → ((p5 ∧ True) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347290531360846503177572621443 : (p3 → (((p5 ∧ True) ∨ (False ∨ ((p3 → p5) ∧ (p2 ∨ p2)))) ∨ (((p2 ∧ ((((p4 ∨ p1) ∨ (p3 ∧ p4)) ∧ False) → p4)) → True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861647725219803314414899312847 : (((((((True ∨ p1) → (((True ∧ p1) ∨ p4) ∨ False)) → ((p2 ∨ (p2 ∧ p4)) ∧ ((p4 → p3) ∨ p1))) → ((p4 → p1) ∨ True)) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ p1) → (((True ∧ p1) ∨ p4) ∨ False)) → ((p2 ∨ (p2 ∧ p4)) ∧ ((p4 → p3) ∨ p1))) → ((p4 → p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
theorem thm_5_vars_655315507772059877473517718869 : (((((p3 ∨ (p1 ∧ (((p4 ∨ False) ∧ (p3 ∧ p5)) ∨ ((p2 ∨ (((True ∨ False) → p5) ∧ p4)) ∧ p4)))) ∧ (p3 → p5)) ∨ (p4 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187332363924825376354636069001 : ((p2 ∧ ((p3 ∨ ((((p2 ∨ p1) → p1) → p5) ∨ p3)) → p3)) → ((((p2 ∨ p2) ∨ (True ∧ p1)) → (((p5 ∨ True) ∧ p1) ∧ p1)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∨ p2) ∨ (True ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44641218685359506159843787558 : (((((((p1 ∨ True) ∧ p3) → p2) ∧ p1) ∨ ((p5 → ((p4 ∨ p2) ∧ ((False ∨ p3) ∨ p1))) → (False → (True ∨ (p2 ∨ False))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696487483634109728953878775100 : ((((((p5 ∨ p3) ∧ (True → (p5 → ((False ∨ False) ∨ p2)))) ∧ p5) ∧ ((p1 → (p5 ∧ p5)) ∧ (((True ∨ p1) ∨ p5) ∨ (p4 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116004977100749202328263591403 : ((((False → False) ∧ (p1 → True)) → ((p4 ∨ p3) → ((((p3 → p2) ∨ ((((p2 ∧ p3) ∨ p5) ∧ False) → p4)) ∨ p5) ∧ False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137447006034716570275309720582 : ((p4 ∧ ((((p5 ∨ True) ∧ (p3 → p1)) ∧ False) ∨ ((((p1 ∨ False) → p2) ∧ p4) ∨ (p3 ∧ (False → (p1 ∨ p4)))))) ∨ (p3 → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40289754935144453525242467716 : ((((p3 → (p3 → (p1 ∨ (((p2 ∨ True) ∨ (((p5 → p2) → (p4 ∨ True)) → False)) → (((p5 ∧ p2) ∨ p5) ∧ p4))))) ∧ True) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112068965828559685327166004331 : ((((p1 → False) ∧ ((((((p5 → (False ∧ ((p2 ∧ p4) ∧ p1))) → p5) ∧ (p4 → p3)) ∨ p3) ∨ (False ∨ p5)) ∨ p1)) ∨ p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40124813484290574747061769018 : (((((((False ∨ ((((p4 ∨ p4) ∧ ((p1 ∧ p4) → p1)) ∧ (p4 ∧ p3)) ∧ p1)) ∧ False) ∧ p4) ∨ (p3 ∧ (p5 ∧ p2))) ∧ p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38160255011910402905808121541 : ((((((p5 ∨ (((p3 ∧ (((p1 → p1) → (p1 → p1)) ∧ p4)) ∧ True) ∧ True)) ∨ p5) ∧ (p4 → p1)) ∨ ((p1 ∧ p4) → p4)) ∧ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104990531125025429981393814346 : ((((p5 ∨ ((True ∧ ((p2 → False) ∧ (True ∧ (p3 ∨ (p5 ∨ p1))))) ∨ (True → p2))) → (p1 ∨ True)) ∧ ((True → False) → False)) ∧ (False → p2)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h16
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166847560936913903575168190147 : ((((((p2 ∧ (False → False)) ∧ ((True ∨ (p4 ∧ p5)) → p1)) ∨ (p4 ∨ p3)) → p3) ∧ p4) → (False ∨ (((p5 ∧ p4) ∧ p5) → (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (((p2 ∧ (False → False)) ∧ ((True ∨ (p4 ∧ p5)) → p1)) ∨ (p4 ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324681499401757322054329344672 : (p5 ∨ ((p2 ∨ (p2 ∧ False)) ∨ (((p3 ∧ False) ∨ (False → (((p5 ∧ p3) ∧ ((p4 ∨ (((p4 ∨ p2) → p4) → p5)) → False)) ∨ p1))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208769303534756314926803137639 : ((p2 ∧ (((p2 → p1) ∨ False) → p3)) → (p3 → ((p4 ∨ (((p5 ∧ p1) ∨ p4) ∨ (True ∨ (p2 → (p4 ∨ (p1 → (p4 ∧ True))))))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
theorem thm_5_vars_303879482828273661392107263344 : (p1 ∨ ((((((True ∧ ((p1 ∨ (True ∧ p4)) ∧ p1)) → (False ∨ True)) ∨ ((p5 ∧ True) → p5)) → p5) ∨ (((p1 ∨ True) ∨ p2) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137833212113502790214243639708 : ((p3 ∨ ((p4 ∨ ((p3 → (p2 ∧ (p3 ∧ (p2 ∧ p2)))) ∧ (p4 → ((p3 → True) → False)))) ∧ (p2 ∧ (p5 → p5)))) ∨ (True ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40415204006909608073378082474 : ((((((p2 → (((False ∧ ((p1 ∨ (p1 → p4)) ∧ (p4 ∧ True))) ∧ p5) ∨ p4)) ∨ p1) → ((p3 → p5) → (False ∨ False))) ∨ p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90213974298136168659223744597 : (((True ∨ (p4 ∨ p5)) → ((((p3 ∨ (p2 → ((False ∧ p1) → (False ∨ ((False ∨ False) → p5))))) ∨ (False ∨ (p2 ∨ p3))) ∨ True) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698535049564425801280637590996 : (((((p4 → (p5 ∨ (p2 → p1))) ∧ (True → (True → (p2 ∧ p2)))) ∨ ((((p3 ∨ (False ∨ (False → (p1 ∨ False)))) → False) ∨ True) ∨ p3)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214520657786552739922277166954 : (((p4 ∧ p4) ∧ (p3 → True)) ∨ (((p3 ∧ p3) → (p4 ∨ True)) ∧ ((False ∨ ((p2 ∨ False) → (p3 ∨ (p2 ∨ (p5 → (p3 → True)))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136780649985195159921616889670 : (((True → p4) ∧ ((False ∨ p5) ∧ ((p5 ∨ p1) ∧ ((p2 ∨ (p2 → (p4 ∧ (p5 → ((p5 ∧ p2) → p1))))) ∧ False)))) ∨ ((False → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147106687112946206333248875510 : ((((False → (p3 ∧ p5)) → ((((((p3 → (p2 ∧ True)) ∨ p2) ∧ p4) → p5) → (p3 ∧ p2)) → p3)) ∧ True) ∨ (((p1 ∨ False) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625584663910076808401905026614 : ((((p1 → (((p5 ∨ p5) ∧ ((((((((False → True) ∨ True) ∨ (True ∧ p1)) ∨ p1) ∧ (p5 → p1)) ∧ p2) → p3) ∧ False)) ∧ p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_692221758630892714429414193341 : ((((((True ∧ (p2 → False)) → (p3 ∧ ((False ∨ p3) ∧ (p3 → p4)))) ∨ p3) ∧ ((((True ∧ (p1 → p1)) ∨ p3) ∨ (p1 ∧ p5)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57381895891050347385170102449 : (((p5 ∧ (p3 → p5)) ∨ ((p1 → (((p1 ∧ ((p5 ∧ p5) ∧ (p4 ∨ p4))) → (False → ((p4 → True) ∨ (False ∨ p3)))) ∨ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328535650175714968332784501095 : (True → ((p4 ∨ ((p2 ∧ p1) ∧ (False ∧ ((((True → True) → False) ∨ (p1 ∨ p5)) ∨ p2)))) ∨ (((p3 ∨ (p3 ∨ False)) → p3) ∨ (p2 ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48392568732267580128573876548 : (((False → (((p4 ∨ ((False ∨ True) ∧ (p5 ∨ False))) ∧ False) → ((((p4 ∧ (False ∧ (False ∨ p4))) ∧ p1) ∨ p4) ∧ p2))) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309806065528468116263055917053 : (p2 ∨ (((False ∨ (True ∨ p5)) → ((((True ∨ (p3 ∨ p2)) → ((p1 ∨ p5) ∨ p3)) ∨ p5) → (p2 ∨ p1))) ∨ ((p4 ∧ True) → (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219879983036584114841390736736 : ((p4 → ((p1 ∧ False) ∧ p3)) → (((p1 ∨ (p1 ∧ False)) ∨ p3) → (((p2 ∧ (((p3 → (p2 ∨ p5)) ∨ (p5 → p4)) ∧ p4)) ∨ True) ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164771392639163609267785102562 : ((((((p1 ∨ (p3 ∨ p5)) → False) ∧ (p2 → p1)) ∨ ((p1 ∨ p3) ∧ (p4 ∧ p3))) ∨ p3) ∨ (p1 → ((p2 ∨ p1) ∨ (True → (p4 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136782360801435873955147076903 : (((False → True) ∧ (((p2 → p2) → (p2 ∨ p2)) ∨ ((((False → p1) ∨ p2) → ((p2 ∧ p4) ∧ (p5 ∧ False))) ∨ True))) ∨ (True ∧ (True ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



