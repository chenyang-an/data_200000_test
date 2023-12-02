variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351523304087494893096031398715 : (p4 → ((((((((p3 → (p5 ∨ p5)) ∧ True) ∨ (p2 ∨ p3)) ∨ p5) ∧ p2) ∧ (p4 ∨ p3)) → False) ∨ (False → ((p3 → (p2 ∧ p1)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164855531965497543310797594013 : (((False ∨ ((p2 ∨ (p4 ∨ True)) → (p4 ∨ (p1 ∧ ((p1 ∧ p5) ∨ (p5 ∨ p1)))))) ∨ p1) ∨ ((False ∧ p4) ∨ (False → (p2 → (p3 → p5))))) := by
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150333576567165819086318639867 : ((p5 → ((False ∧ (False ∨ (p2 ∨ (((p4 → p5) ∧ (True ∨ p1)) ∧ (((p3 ∧ p2) ∨ False) ∨ p3))))) ∨ p1)) ∨ ((False ∧ p5) → (p2 ∨ True))) := by
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
theorem thm_5_vars_209565705334190134335263162823 : ((p5 → ((p5 ∧ (p4 ∧ p2)) → True)) → (((((((p5 ∧ p1) ∨ False) ∧ p1) ∧ False) ∨ p2) ∨ (p3 ∨ True)) ∨ (((True → p3) ∧ p4) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48858807650783080114703584297 : (((p3 ∨ (p1 ∨ (((p1 → p2) ∨ ((((p4 ∧ p1) ∨ p2) → p4) ∨ (p5 → ((p1 ∨ p3) → p3)))) ∨ True))) ∧ ((p5 ∧ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184920811388336991544438258712 : (((p1 ∧ (False ∨ p5)) ∨ (p1 ∧ ((p5 ∧ False) ∨ (False → p3)))) ∨ (((False ∧ p5) ∧ (p2 ∧ (True ∨ p3))) → (p1 ∧ (p2 ∨ (False ∧ True))))) := by
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
theorem thm_5_vars_345544234116281904930387187149 : (p3 → (((((p5 → p5) → p5) ∨ (p2 ∧ p2)) ∧ ((p4 ∨ (True ∨ ((p3 ∨ p3) ∨ (((p3 → p4) ∨ False) → (p1 → p1))))) ∧ False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113472091918412842183651848953 : ((((p4 → ((p1 ∧ True) ∧ (p5 ∧ (((False → ((p5 ∧ p4) → p1)) → ((p5 ∨ False) → p3)) → p4)))) → p5) ∨ (p1 ∨ True)) ∨ (p3 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206148613212350012304176426250 : ((p5 ∧ (((p5 ∨ p4) ∧ p3) ∧ p4)) ∨ (((p2 ∨ True) ∧ (((p4 → p4) ∨ True) → p2)) → ((True ∧ ((True ∨ p4) ∨ p5)) ∨ (p1 ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148458848072165623033634129061 : ((((p4 ∨ ((p5 ∧ False) ∧ (False ∨ p1))) ∨ ((p5 ∨ p5) ∨ p4)) ∧ (((p2 ∧ False) ∨ (p1 ∨ p5)) ∨ p3)) ∨ (p4 ∨ (False ∨ (p5 → True)))) := by
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
theorem thm_5_vars_112502601344425610836266254317 : ((((p5 → ((((((True ∨ (p3 ∧ False)) → True) ∨ (p2 → (p4 ∨ p4))) ∧ (p2 → p4)) ∧ p2) ∧ (p3 ∨ True))) ∨ True) → False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51245501080743929148090252360 : (((((p3 ∨ p2) → p4) → ((p2 ∧ (p1 ∨ ((p1 ∧ p3) → p4))) ∨ ((p4 ∧ p3) ∨ False))) ∨ (True → ((True ∧ (p1 ∧ p4)) → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258766548069553935737552856111 : ((True → False) → ((p2 ∧ ((p5 ∨ (True ∨ p5)) → ((p2 → (((p3 ∧ p2) ∧ True) → p3)) → ((p5 → ((p1 ∧ p1) ∧ p3)) ∨ True)))) ∨ p5)) := by
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
theorem thm_5_vars_157561298206933093216233688661 : (((((((True ∧ p2) ∧ p2) → False) ∧ (p1 → False)) ∧ (p4 ∨ (p4 ∧ (p4 ∧ False)))) → (p5 ∧ p4)) ∨ ((((p2 → p1) ∧ p1) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196796207576341228220529816704 : ((((p5 ∨ p2) ∨ ((p3 → p2) → p3)) ∧ True) ∨ (((True ∨ ((True ∧ p5) → (p5 ∧ True))) ∧ True) ∨ (((True ∧ p1) ∨ (False ∧ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51284873959181641925256409098 : (((p3 ∧ ((((p2 ∧ ((p3 → (p4 ∨ p2)) ∨ (False ∧ False))) → p4) ∧ (True ∧ p2)) ∧ p3)) ∨ ((p5 ∨ (True ∨ (p1 ∨ p2))) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689953740926765173248299755174 : ((((False ∧ ((((p3 ∨ ((p4 ∨ p4) ∧ (True ∧ p1))) ∧ p1) → (False ∨ p4)) ∧ p5)) ∨ (p4 ∨ (p3 ∧ (p1 → ((p5 → p5) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258705053379629431988275270729 : ((True → True) → ((((p5 ∨ False) → p3) → ((((p4 ∧ p3) ∧ (p3 ∧ p4)) ∨ p1) ∨ ((p5 → (True → p4)) ∨ (p5 ∨ (p3 → True))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319499583983438694144501210989 : (p4 ∨ ((p3 ∨ ((p3 ∨ p5) ∨ ((((True → p3) → False) → p1) ∧ True))) → ((p2 → p4) ∨ (p4 → (p3 ∨ (p5 ∨ ((True → p2) ∨ p4))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130108011938161061760564341338 : ((((((((p1 ∧ (p3 → (p5 → True))) ∧ True) ∨ ((p4 ∨ p1) ∨ p2)) ∨ p5) → p1) ∧ (p1 ∨ p2)) ∨ (True ∨ p2)) ∧ (p3 → (p3 ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698071967443734611678217108485 : ((((((False ∨ p5) ∨ (p5 → ((p5 ∧ (p2 ∨ p3)) ∨ p4))) ∨ p3) ∨ ((p5 → (False ∧ (p3 ∨ p1))) ∨ (True ∨ ((p4 ∧ p3) ∧ p1)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_61060301415795895403587933655 : ((False ∧ (((True → p4) ∧ (((p5 → p2) → False) ∨ ((p2 ∧ p4) ∨ ((((p3 ∧ False) ∧ p3) → p4) → p3)))) ∧ ((False ∧ p2) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718494705754699260381994263446 : (((((p1 ∨ (p1 ∧ False)) → p5) ∨ (True ∧ ((p3 → True) ∧ ((((p5 ∨ (p1 ∨ p3)) ∧ ((p4 ∧ (p2 ∨ p2)) ∨ p1)) ∨ p2) ∨ True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64945015796745830452010070970 : ((p2 ∨ (((True ∧ (p2 ∨ (p3 ∨ p2))) ∨ (p4 → (p5 ∧ p2))) ∧ ((p3 ∧ p2) ∧ ((True ∨ p4) → ((p1 → False) ∧ (p2 ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47067753813698259610819395466 : (((((p4 ∨ False) ∨ ((p4 ∨ (((True ∨ False) ∨ p3) → (True → (((False ∨ p2) ∧ p4) ∨ p4)))) ∧ True)) ∨ (p3 ∨ True)) ∨ (p5 ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114006409937812301379942064431 : (((((p3 ∨ ((p1 ∨ p1) ∨ ((p4 → True) ∨ (True ∨ p4)))) ∨ (p3 → (False ∨ (p4 → False)))) ∧ p1) ∨ (p4 ∧ (p2 ∧ True))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244179780053139569034684958334 : ((True ∧ p4) ∨ (p3 → (p4 ∨ ((((True → p5) ∨ True) → (((False ∨ (p1 ∨ p5)) ∧ (p4 ∨ p2)) ∨ (p4 → (True ∨ p5)))) ∨ (p3 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_674529769651816754159603232365 : ((((p5 ∨ (((p4 ∨ ((True ∨ p4) → p1)) ∨ False) → (((((p3 ∨ p4) ∧ p4) ∨ (p4 → True)) ∧ p1) ∧ False))) → ((p3 ∧ p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256761086907855353573712227240 : ((p1 ∨ p2) → ((((p1 ∨ ((p3 ∧ p3) → p4)) ∧ (p3 ∧ p1)) ∨ (p1 ∨ (((p3 ∧ p1) → ((p2 ∨ (True ∧ p2)) ∨ p3)) → p2))) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179142089853366161790669282140 : ((p1 ∧ (p4 ∨ ((((p2 ∨ (p1 → False)) ∨ p3) ∧ True) → (p3 ∨ p4)))) ∨ (p4 ∨ (((p3 → p5) → p1) → (((p5 ∨ False) ∧ p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147029242176528929973561908067 : ((((((((p2 → False) ∨ p1) ∨ True) → p1) → (p1 ∨ (p5 ∨ (p2 → p1)))) ∨ ((True ∧ True) ∧ True)) ∧ True) ∨ (p2 ∨ ((p5 → p5) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645043809320130929406935230014 : ((((p3 ∨ ((True → ((True → (((True → True) ∨ (p3 → (False ∧ False))) ∨ ((((p4 ∧ p5) ∧ p1) → p5) ∨ p5))) ∨ p3)) ∧ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769872408534058036080166864298 : (((p5 ∧ (p5 ∨ (p2 ∨ (((p2 ∧ ((True ∨ p2) ∨ p3)) ∨ (((False ∧ p5) → p1) ∨ ((False ∨ p3) ∨ ((p3 ∧ p4) ∨ p3)))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194867214891859186291924120938 : ((((p5 ∧ (p2 ∧ (p3 → p3))) ∨ p1) → True) ∧ ((p2 ∧ ((False → False) → (p2 ∧ ((p4 ∧ (((p1 ∧ False) ∨ p3) → p4)) ∧ p1)))) ∨ True)) := by
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
theorem thm_5_vars_41318673121668751471290923312 : ((((((p2 ∧ p1) ∧ False) ∨ ((p2 ∧ (((True ∧ (False → p5)) ∧ p4) ∧ False)) ∧ p2)) ∧ ((p1 ∨ ((p4 ∧ p5) → p4)) → True)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716116539873223631560137704817 : ((((((p3 ∨ p3) → p2) → p5) ∧ ((True → ((p4 ∧ p1) ∨ ((((p4 → (False → p1)) ∨ (p4 → p1)) ∧ (p1 → p5)) → p4))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693702162266417284179636842013 : ((((((p1 → p5) ∨ (p4 → ((False ∧ p2) ∨ (p1 ∧ (p2 ∨ p2))))) ∨ p2) ∨ (((p1 ∨ (p5 → True)) ∧ ((False ∧ p3) ∧ p4)) → p5)) ∨ p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89026366812334796725198631022 : ((((True → p2) ∧ p5) ∧ (p2 → ((((p5 ∨ True) ∧ (False ∨ (((True → p2) ∨ False) → ((p5 ∨ p4) → (p1 → p1))))) → p4) → True))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697193319593020422386966487953 : ((((((p1 → p5) ∧ p5) ∨ ((p1 → True) → ((p2 → p3) → p2))) ∧ (p5 ∧ (p4 ∨ (False ∨ (p5 ∨ (p4 ∧ (False ∧ (False ∧ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42241097666132763010668470597 : (((False ∧ (p3 ∧ (p4 ∨ ((p5 → (p2 ∧ ((((True ∧ (False ∧ (True ∨ p2))) ∧ p3) ∨ (p3 ∧ p4)) ∨ p4))) ∨ (True → False))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300362247028699067041634985346 : (False ∨ ((((p2 ∧ True) → (True ∧ (((p5 ∧ (False ∧ (((False ∧ True) ∨ (False ∧ p1)) ∨ p2))) ∨ p5) ∨ True))) ∨ False) ∨ (p2 → (False ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659220286112198573526860617864 : ((((p4 → ((((((p3 ∧ p5) ∧ p3) → ((p5 ∨ ((False ∨ True) ∧ p4)) ∧ True)) ∨ (True ∧ p5)) → p4) → (p2 ∨ False))) ∨ (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171334691478921446481072153298 : ((((((p3 ∧ (p5 → ((p4 ∨ (p1 ∨ p5)) → p5))) ∨ p1) ∧ True) → p5) ∧ p5) ∨ ((True ∨ (p5 ∨ (p2 ∨ (False ∨ True)))) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173172469634025212078524824969 : ((p4 ∨ (((p5 ∨ p3) ∨ ((p2 ∧ ((p1 ∨ (p4 ∨ p4)) → p2)) → False)) → p2)) ∨ ((False ∧ (p4 ∨ False)) → (p4 → (False → (p4 → p3))))) := by
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
theorem thm_5_vars_308525650422231619299581183556 : (p2 ∨ (((((p2 ∧ (((True → p1) ∧ p5) ∧ True)) ∧ p2) ∧ (False ∨ (p4 → False))) ∨ (p4 → ((p4 → (p4 → True)) ∨ (p1 ∧ p2)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637782240493158338876998938238 : (((((p4 ∨ (((p4 ∨ (p3 ∨ p1)) ∧ (p2 ∧ p4)) → p3)) → (False ∧ ((p4 ∧ (True → p4)) → (p2 ∨ (p5 ∨ (p5 ∨ p1)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65213182103470642988034302099 : ((p3 ∨ ((((((False ∧ (p4 → p4)) → p5) ∨ (((True ∨ False) ∧ p4) ∧ p2)) → p4) ∨ ((p2 → (False ∨ p1)) ∨ (True ∨ p4))) ∨ p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_336252552583919029121101334266 : (p1 → ((((p2 ∧ (True → ((((True ∨ (True → p4)) ∧ p1) ∨ (p5 ∨ p5)) ∨ p1))) ∧ p3) ∨ ((p5 ∧ (p2 ∨ False)) ∨ (True → p1))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165892672015567697418016990833 : ((((p4 → p2) → p5) → (((True ∨ p2) ∨ True) → (((p4 ∧ p2) → (p4 → p2)) ∧ p1))) ∨ ((p3 ∧ p4) ∨ ((True ∨ (True → False)) ∨ p4))) := by
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
theorem thm_5_vars_137872443800487104276728477548 : ((p3 ∨ (p3 → (p5 ∧ (((((((p2 ∨ ((True ∨ p3) ∨ True)) → p2) ∧ False) ∧ p1) ∧ p2) ∨ (p4 ∧ p2)) ∧ False)))) ∨ ((p5 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114118491626115661871924113327 : (((p5 ∨ ((False → (False ∨ p4)) → (((False ∨ p4) → p2) ∨ (p4 ∨ (p1 ∨ (p5 → (p1 ∧ p2))))))) ∨ (p5 ∧ (True ∨ True))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126586093581122806661357519983 : ((p3 ∧ ((((p3 → (((False → (p1 ∧ False)) → p4) ∧ False)) → p3) ∧ (p3 → (True ∨ (p3 → p2)))) ∧ (True ∨ (True ∨ p4)))) → (p1 ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
theorem thm_5_vars_246381647179185009006230096583 : ((p5 ∧ True) ∨ (((p3 → (((p5 ∧ (True ∨ p2)) ∨ ((p5 → p5) ∨ p3)) ∧ p3)) ∧ ((p4 → True) → ((False → (p3 ∨ True)) ∧ p5))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199960423396396092133151977164 : (((True → (p4 ∨ (p5 → p1))) ∨ (p4 ∨ p4)) → (((((p2 ∨ ((p2 ∧ p2) ∧ (p4 ∧ (p2 ∧ p4)))) ∧ p4) → True) → (p5 ∧ p1)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (((p2 ∨ ((p2 ∧ p2) ∧ (p4 ∧ (p2 ∧ p4)))) ∧ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (((p2 ∨ ((p2 ∧ p2) ∧ (p4 ∧ (p2 ∧ p4)))) ∧ p4) → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (((p2 ∨ ((p2 ∧ p2) ∧ (p4 ∧ (p2 ∧ p4)))) ∧ p4) → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192706358762662125828141026891 : (((((True ∧ p2) ∨ True) ∧ (p4 ∧ (p5 ∧ True))) → p4) → (((p4 ∨ (((((p3 ∧ p4) → p3) ∨ True) ∨ (p1 ∨ p1)) ∨ p4)) → p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ (((((p3 ∧ p4) → p3) ∨ True) ∨ (p1 ∨ p1)) ∨ p4)) := by
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244739232546733820574121353582 : ((p1 ∧ False) ∨ ((p5 → ((((True → p3) ∧ (p5 → ((p2 ∧ p4) → (False → (p2 ∨ ((p4 → True) ∧ (p3 ∨ p4))))))) ∧ p5) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699134889244570339579114957007 : ((((True → (p3 ∧ ((((p4 ∨ p3) → (False ∨ p2)) ∨ p4) ∧ False))) ∨ (p5 ∧ (p5 → (p5 ∧ (((p5 ∧ False) → p5) → (p1 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335885174515012759323733860793 : (p1 → (((p1 ∧ ((False ∧ p4) → p4)) ∧ ((p1 → ((((True → (p4 → True)) ∨ p5) ∨ p5) → ((p4 ∨ (p2 → True)) ∧ False))) ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197997480469282080809077397885 : (((True → False) ∧ ((p2 ∧ (True ∨ p1)) ∨ p4)) ∨ (((p4 → ((p3 ∨ p1) ∧ ((((p3 ∨ p1) → p3) → False) ∨ p3))) → p1) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143901291770046946285280421326 : (((((p1 ∨ ((((p5 ∧ (p1 → p2)) → p1) ∧ p4) ∨ False)) ∨ p1) → ((p5 ∨ (p2 ∨ p1)) ∧ p4)) ∨ True) ∧ (((p5 ∧ p2) → p3) ∨ True)) := by
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
theorem thm_5_vars_678529605243561972150716890550 : ((((((p2 ∧ p4) → p5) ∨ (((True → p5) ∨ (True ∧ ((p2 ∧ p4) ∧ ((False ∧ p3) ∨ False)))) ∧ False)) ∨ ((p1 ∧ True) → (p1 ∨ p3))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205155947066883361487995049832 : (((p1 ∧ (p2 ∨ p5)) ∧ (False ∧ p3)) ∨ (p3 → (False → ((True ∨ (((((p4 → p4) → (p3 ∨ True)) ∨ False) ∧ (False → p3)) ∨ p3)) ∧ p5)))) := by
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
theorem thm_5_vars_310124177276568038841907092636 : (p2 ∨ (((p4 ∨ ((p5 → (False ∧ p2)) → p5)) ∨ (p3 → (p3 → (p5 ∧ p1)))) ∨ ((p3 ∧ True) → (((p3 ∧ p4) ∨ (p4 ∧ p5)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856140643983090026793288940170 : ((((((((p5 ∨ (p1 ∧ True)) ∨ (False ∨ p3)) → ((False ∧ False) ∧ (False ∧ (p4 ∨ (False → p2))))) ∨ (p2 ∧ (p5 → p2))) ∨ True) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∨ (p1 ∧ True)) ∨ (False ∨ p3)) → ((False ∧ False) ∧ (False ∧ (p4 ∨ (False → p2))))) ∨ (p2 ∧ (p5 → p2))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225214628204200373537994399701 : (((p5 ∧ False) ∧ p1) ∨ ((True → False) → ((((p3 ∧ False) ∨ (False ∧ (p4 → (p5 ∨ ((True ∨ (p5 → (p2 → p5))) ∨ p3))))) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300733038635989739410912474193 : (False ∨ ((True → (p1 ∧ ((p5 ∧ p3) ∨ ((False ∧ (p5 ∧ p2)) ∧ (((False → p4) ∨ True) → p2))))) → ((p1 ∧ ((p5 ∨ p2) ∨ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148567610007935969915741326153 : (((p4 ∧ (((p2 ∧ (False → (p5 → p3))) ∧ p1) ∨ False)) ∧ (((p4 ∧ p1) ∧ ((p1 → p1) → True)) ∧ p2)) ∨ ((p5 ∨ (p2 ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317884653758597277563727681053 : (p4 ∨ ((True ∧ (p2 ∧ (True ∧ (False ∧ (((p4 ∧ ((p1 ∨ p3) ∨ p1)) → p1) ∨ ((p2 → p1) → (p2 ∧ ((False ∨ True) → p1)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258803469235509877439810179548 : ((True → False) → (p2 ∧ (False ∧ ((p3 ∨ (p3 ∨ (True → True))) ∧ ((p4 ∨ (False → (p1 ∧ p1))) → (p1 → ((False ∨ (True → p3)) ∨ p4))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117269989399290322473507689212 : ((False ∧ ((p3 ∧ (((True → p1) ∧ p1) ∨ (((p5 ∧ True) ∨ p5) → (p2 ∨ ((p1 ∧ (False ∨ (p1 → p1))) ∧ p4))))) ∧ p5)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611815788513515117148494856048 : (((((p2 → ((p4 ∧ p2) ∨ (p5 ∨ (((((p1 ∧ (p1 → p1)) ∨ p2) ∨ (False ∨ p5)) → (p4 ∧ (False ∨ p1))) → p5)))) → False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_161844235058399330273455076776 : ((True → (((p4 ∧ (p3 ∧ p4)) ∧ p2) ∧ ((p3 ∧ p4) ∧ ((True ∨ p1) → ((p4 → True) → p2))))) → (((p3 → p2) ∧ (p4 → p4)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659118161856618783633171719694 : ((((p3 → ((((p4 → ((False → False) ∨ (((p5 ∨ ((p4 → p3) ∨ p4)) ∨ (p3 ∨ p1)) → p5))) ∧ p4) → p1) ∧ p5)) ∨ (True → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233626357858811854849825257369 : ((p2 ∨ (p5 ∧ p1)) → (((((p5 ∨ (p4 ∨ p1)) ∧ p4) ∧ True) ∨ (((p5 ∧ p3) ∨ ((p1 ∨ p3) → (p5 ∨ (p2 ∧ p2)))) → p1)) ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57968344550011218621976703245 : (((p3 → (p1 ∧ p1)) → (((((p5 ∨ ((p4 → p1) ∨ (False ∨ (p2 ∨ (p3 ∨ p1))))) ∨ (p2 ∧ (p4 → p4))) ∨ True) → p2) → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∨ ((p4 → p1) ∨ (False ∨ (p2 ∨ (p3 ∨ p1))))) ∨ (p2 ∧ (p4 → p4))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178546042693556576727922518785 : (((p2 → ((False ∨ p3) ∨ ((p3 → p4) ∧ p3))) → (p3 ∨ (p2 ∧ p4))) ∨ (((p4 ∨ (p1 → False)) ∨ (((p2 → p2) ∨ p4) ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158950563813193967219698969466 : ((p2 ∨ (((p5 → p3) → p3) → (((True ∧ p3) ∧ (p5 ∧ (True ∨ True))) ∨ (p2 ∨ (p4 ∧ p5))))) ∨ ((p5 → p4) ∨ ((p5 ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115437859707907527819505506173 : (((((p1 ∨ (p5 ∧ p1)) ∧ p2) ∧ (p4 ∧ False)) ∨ (((((False → (((False ∨ p2) → False) → True)) ∧ False) ∨ p4) ∧ False) → True)) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156939332656202684487162356122 : (((((((p1 ∧ (p3 ∨ p1)) ∧ (p5 → p4)) ∧ False) ∨ (p4 ∧ (p1 ∨ True))) ∨ (p4 ∨ p1)) ∨ False) ∨ (((p2 ∧ p1) → (p5 → p2)) ∨ False)) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327129128825660457529316853850 : (True → ((True ∧ (((p1 ∨ (True ∨ (((True ∧ p5) ∧ (p2 → True)) → True))) ∨ p5) → (((False ∧ (p5 → True)) ∧ p3) ∨ (p4 → p4)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166129220322739285801155022437 : ((True ∧ ((p4 → ((True ∧ (p1 → True)) ∧ (True ∧ p1))) → ((p2 ∧ (p3 ∧ p2)) ∧ p1))) ∨ (False → ((((False → p5) → False) ∧ p3) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226572555870385459187205365025 : (((p4 → p3) ∨ p5) ∨ (((p1 ∧ (((p2 ∨ True) → p2) ∨ (False ∨ p1))) → (p5 ∨ (p4 ∧ (p2 → ((p5 → (False ∨ True)) ∨ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392286613857702167462189315908 : (((((p4 ∧ (p2 ∨ False)) ∧ ((((False → (p5 ∧ ((False → p5) ∧ (((p5 ∧ p5) ∧ (p1 → p5)) ∨ p1)))) ∧ p2) ∧ p4) → False)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_687914725602162301574936197558 : (((((((False ∨ (True ∨ (p4 ∨ p4))) ∧ p1) ∨ p2) ∧ ((False ∨ False) ∧ (p2 ∨ False))) ∧ (p2 → ((p3 ∨ p3) ∨ (p1 ∧ (p5 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192405433678640694327074122136 : (((((p3 ∧ ((p4 ∨ p4) ∨ p1)) ∨ True) ∨ p1) ∨ p5) → ((((p4 → (p2 ∨ (p4 ∨ (False ∧ ((True ∨ p5) → p3))))) ∨ p4) ∧ True) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173928221038628806189785569630 : (((((p2 → p2) ∨ (((p5 ∧ p3) → p1) ∧ (p4 → p2))) ∨ (False ∨ p4)) → False) → ((p5 ∧ (p5 ∨ True)) ∨ ((p1 → (p1 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148688936683604694428186307635 : (((False ∧ (False ∧ ((p4 ∧ (p4 ∨ p1)) ∨ p5))) ∨ (p1 → (((p1 ∨ True) ∧ True) ∨ ((True ∨ True) ∧ p5)))) ∨ ((p5 ∧ p1) → (True ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157279214312584203466645322713 : ((((p1 ∧ p1) ∧ (p4 ∧ (p3 → ((False → False) → (p1 → ((False ∧ p4) → (p4 → p4))))))) → False) ∨ (p2 → ((False ∨ (p2 → p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250093146224639460685659711299 : ((True → p4) ∨ ((((p4 ∨ p2) → ((p1 ∨ False) ∨ True)) → (((((p5 ∨ p5) → (p5 ∧ p5)) ∧ p1) ∧ (True → p3)) ∧ False)) → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p2) → ((p1 ∨ False) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314442246967059331223080961624 : (p3 ∨ ((True → (((((True ∧ (p5 ∧ p1)) ∧ (False → (False ∧ p1))) ∨ (p3 → True)) ∨ (False → p2)) → p1)) ∨ ((True ∨ p5) ∨ (True ∧ p3)))) := by
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
theorem thm_5_vars_112368187065816623700271594345 : ((((((False ∧ p5) ∧ ((((p3 ∨ (p5 ∧ True)) ∧ p3) ∧ ((p3 → (True ∨ p2)) ∨ (True → p3))) ∨ p3)) → p4) ∧ True) → p2) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342002666886048363919443293941 : (p2 → (((p1 → p4) ∧ (p4 ∨ ((True ∨ p4) → (((True ∧ (p5 ∨ p1)) → (p5 ∧ p4)) ∨ ((p3 → p4) ∨ p4))))) ∨ (p5 ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116743678197733567736501758244 : (((p4 ∧ p4) ∨ ((p4 ∨ ((p4 ∧ (p3 ∧ ((p4 ∨ p3) ∧ p5))) ∨ ((p5 ∨ ((False → p3) → p4)) → (True ∨ p1)))) ∨ p4)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231811544619042166363977458971 : (((p4 ∧ p4) → p2) → (p2 → (((p3 ∨ p5) → ((p3 ∧ (p5 ∧ p4)) ∧ p1)) → (p3 → ((((p1 ∧ (p2 → p1)) → True) → p2) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147417299625790846047234222405 : ((((p3 ∧ (True ∧ (True ∧ p1))) → ((False ∧ (p4 ∧ (p2 ∧ (((True ∨ p4) ∨ p5) → False)))) ∨ p5)) ∨ p3) ∨ (True ∧ ((p4 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248788240300258823995011255291 : ((p3 ∨ p3) ∨ (p2 ∨ ((p4 ∨ ((p3 ∧ (False ∨ (p5 → (((p2 ∧ False) → False) → (p3 ∧ (((p2 → p1) ∧ False) → p5)))))) ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199974375027810485856679844947 : (((((False ∨ p3) ∨ p3) ∧ True) → (False → p5)) → (((((p3 ∧ True) ∨ p1) ∧ p5) ∧ (((False → p3) ∧ p1) ∨ (True ∧ (p4 → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700525743582377374422611411561 : ((((p4 ∨ (p1 ∧ (((((p4 → p3) ∨ p3) ∨ True) ∧ True) → False))) → ((p5 ∧ (p5 → p3)) ∨ (((p3 ∨ False) ∨ (p5 ∨ p5)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187747537659838986955755604100 : ((p2 → (((False ∨ (False → ((p1 ∧ False) ∧ True))) → p4) ∨ p4)) → (p1 → (((((False ∨ p5) ∧ p3) → (p2 ∧ False)) → p4) ∨ (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323782398805144859932138444231 : (p5 ∨ (((((False ∨ p2) ∨ False) ∧ (p2 → (p3 → (((p3 ∨ (True → p3)) → p5) ∧ p3)))) ∨ p4) ∨ ((((p4 → p5) ∨ p3) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



