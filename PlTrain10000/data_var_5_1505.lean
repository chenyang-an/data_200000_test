variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310530025175857915422437419492 : (p2 ∨ (((((p5 → p1) → p2) → True) → False) → ((((p5 → ((((p1 → True) → p5) → p4) ∧ p2)) ∧ (p3 ∧ True)) → p1) ∨ (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p1) → p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639041396438502928276047021030 : ((((((p5 ∨ (p4 ∧ p4)) ∧ p5) ∨ ((((p2 ∨ True) ∧ (p3 ∧ (p3 ∨ ((False ∨ False) → True)))) → p4) ∨ (p1 → (True ∨ True)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64907674935104472319533418595 : ((p2 ∨ (((p4 ∨ ((p1 ∧ (p3 → p1)) ∨ False)) ∨ (p5 → ((p4 ∨ (p5 ∧ False)) → (True ∨ p5)))) ∨ ((p2 ∨ (p3 ∨ False)) → p5))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603543867507675845074404979969 : ((((p3 ∨ ((True ∧ p1) ∨ ((p2 ∧ p1) ∧ (True → ((p1 ∨ False) → (p1 ∧ (p3 ∨ ((p2 → (p1 ∨ (p1 ∧ p5))) ∨ p2)))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342291028106165125933718141460 : (p2 → (((p5 → (p1 ∨ p4)) ∧ ((((p1 ∨ False) ∨ True) ∨ ((p3 → p4) → p2)) ∧ (p1 → p2))) ∨ ((False ∨ (p2 ∧ (True → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228468153244826127989422036078 : ((False ∨ (p4 ∨ p5)) ∨ (p5 ∨ ((True → ((((p3 ∨ p3) ∨ True) → p2) ∧ ((((p5 → False) ∧ p2) ∨ (p1 → p5)) → (p1 ∧ p3)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  have h5 : ((p3 ∨ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_12900065913871734244923933986 : (((p1 ∧ (True → (p2 ∧ ((((((((p2 ∨ True) ∨ p2) ∨ True) ∧ (p1 ∨ p4)) ∧ p3) ∨ p4) ∨ ((p1 ∨ p1) ∧ p1)) ∧ p5)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60458301798140598902499705785 : (((p5 → p2) → (((p3 ∨ (False → ((p5 → p2) ∧ p3))) ∧ (p3 → (((p1 → (False ∧ p1)) ∨ p4) ∨ (p3 ∨ (p3 → True))))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309332286616692080690757902859 : (p2 ∨ (((((((p4 ∧ p2) → (((p2 ∧ p3) ∨ ((p5 ∨ True) ∨ (True ∧ False))) ∧ p4)) ∨ p4) ∧ p5) → p2) ∨ (p4 ∨ True)) ∨ (False ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114745572385084607973506612787 : ((((True ∧ p5) → ((True → False) ∨ ((((True ∨ p5) → (p4 → False)) → True) ∨ p1))) → ((p4 → p1) ∨ ((p4 → p4) ∨ p5))) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194182994484575669002757618358 : ((p2 → (False ∧ (p1 → (p1 → ((p1 ∨ p2) ∨ p4))))) → (((((False → False) ∧ ((True → False) ∧ True)) ∨ False) ∧ ((False ∨ p5) ∧ p4)) → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h4.left
    let h11 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635178609848232780042270804764 : ((((((p1 → p3) → (p1 ∨ (((p4 ∨ p1) → ((False → (p3 → p3)) → ((True ∧ p4) ∧ True))) → p1))) → (p4 ∧ (p4 ∧ False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165300700301488106296660539458 : ((((False ∧ p1) → (((True ∧ (False ∧ False)) → (p1 ∨ p1)) → (p1 ∨ p1))) → (p1 ∧ True)) ∨ ((p3 ∧ (p3 ∨ p1)) ∨ (p4 ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356158053412541630534223999910 : (p5 → (((p3 → ((p3 → (True ∧ p1)) → p4)) → (p1 ∨ (p2 ∧ (p1 ∨ ((False ∨ p2) ∨ False))))) ∨ ((p5 → ((p2 ∨ p2) ∧ p3)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313364082270382622326573232808 : (p3 ∨ ((p3 → (p5 → (((False → (p1 ∨ (p5 ∧ p5))) ∧ True) ∧ (((p5 → (p2 ∨ (p3 ∨ p2))) ∧ p1) ∧ ((p1 ∧ p1) ∨ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113973395655817657077476676745 : (((p4 ∧ ((p2 ∧ (p5 ∧ True)) ∨ (((p4 ∨ (False ∨ ((p1 ∧ True) ∨ p3))) ∨ p4) ∨ (p4 ∨ True)))) ∧ (True → (p3 → p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196482664197033586460602682042 : ((p1 → (True ∧ (p2 → (p3 ∨ (p2 ∨ p4))))) ∧ ((p1 ∨ ((p3 → (((p2 ∨ p3) ∧ p4) ∨ False)) ∨ (p4 → (p4 ∧ True)))) ∨ (True ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178891137974795685300546518869 : (((True ∨ p1) ∧ ((True ∨ p4) → ((p1 → ((p1 ∧ True) ∨ p4)) → p5))) ∨ (p1 → (p2 ∨ (((p3 → p2) ∧ p1) → ((True → p3) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254573716045676821955419960581 : ((p3 ∧ p1) → (((p3 ∧ (((((p1 ∨ p5) → True) → p4) ∨ (p3 ∨ (((p1 ∧ p3) ∧ False) → (p5 ∧ p3)))) → p5)) ∨ (p2 → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54099554726768517903094688888 : (((True ∧ (False ∨ ((p4 → (p3 → p3)) → (False ∧ False)))) → (p2 ∨ (p4 ∧ (((False ∨ p5) ∧ (False ∨ False)) ∨ (True → (p5 ∧ p2)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p4 → (p3 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h6
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197542678781730197885679154229 : ((((p1 ∧ (False ∨ p4)) ∨ False) ∨ (p4 ∨ True)) ∨ ((((((p1 → True) ∧ (p2 ∨ p5)) → (p1 ∧ ((p2 ∧ p1) ∧ p2))) ∨ p2) → False) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219193120732436847672395241704 : ((False ∨ (p4 ∧ (p2 ∨ p1))) → (p5 → (((p2 → False) ∨ (p1 ∨ (((((p2 ∨ True) ∧ p3) ∨ (False → False)) ∧ (p3 ∧ p3)) ∨ p4))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46477652375041892019390263630 : ((((p4 → (p1 → p4)) ∧ ((((p3 ∧ True) → p4) ∨ ((p2 → (p1 ∨ p4)) ∨ (p4 → (False → (False ∨ True))))) ∧ True)) ∧ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42731731382704623120518389329 : (((True → (((p2 ∨ False) ∨ ((p3 → ((p1 ∧ ((False → p3) ∨ False)) ∧ (p5 ∧ p2))) ∨ (p3 → ((p2 ∧ p1) ∧ p5)))) → p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135607217496473697461649028319 : ((((False → p1) → (((((p2 → (p3 ∨ (p1 ∨ p3))) ∧ p4) → True) → p3) ∨ True)) ∨ (p3 → ((p4 → p1) → p5))) ∨ (True ∧ (p4 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42179790862186025030240112120 : (((True ∧ ((((p3 ∧ ((p2 ∧ (p4 ∧ p1)) → False)) ∨ ((p3 → (p1 ∨ p3)) ∨ True)) → (p3 → (p3 → (p5 ∧ p5)))) → p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747436423904456034239418082575 : ((((True → False) → (((p2 ∨ False) ∧ (True → ((False ∨ ((p2 ∨ p3) ∨ ((p4 → p1) → ((True ∧ p5) ∨ p5)))) ∧ (p2 → p5)))) ∧ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116707557224490608277607131854 : (((p1 ∧ p2) ∨ (((p1 → (p3 ∧ (False ∨ (True ∨ (True ∧ False))))) ∨ (True ∧ (((p3 ∧ (p1 ∨ p2)) → p1) ∨ False))) → p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200398370290696019684472935094 : (((p2 ∧ p2) ∨ (p4 ∨ ((p1 ∧ True) ∨ p5))) → ((((p5 → p2) ∧ p2) ∨ ((p3 ∧ p5) → True)) ∨ (p1 → ((p4 ∨ True) ∨ (p2 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47063617283183678166258719291 : (((((((p1 → (False ∨ (p4 → p2))) → p2) ∧ p1) ∧ ((((p2 → p4) ∨ True) → (p1 ∨ p3)) ∨ p5)) ∨ (p1 ∨ True)) ∨ (p2 → p2)) ∨ p1) := by
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
theorem thm_5_vars_156995455880642443412878440384 : ((((p3 ∧ (True → (p5 ∧ True))) ∧ ((((((p2 ∧ p5) ∧ True) → p5) ∨ False) → p2) ∧ p3)) ∨ True) ∨ ((p2 → (p1 ∧ (p5 ∨ p1))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114584259271360145658927806842 : ((((p2 → ((True → False) ∧ p4)) ∨ (((p2 ∧ p2) → ((False ∧ True) → p5)) ∨ p5)) ∧ ((p5 → (p2 ∧ False)) ∨ (p4 ∨ p3))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783219865715317626878251184320 : (((p3 ∨ ((((False ∧ (p4 ∧ True)) → ((((p3 → (False → p4)) → p3) ∧ p4) ∨ p3)) → ((p5 ∧ True) ∨ p3)) → (p1 → (p5 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299282206354473482391412407434 : (False ∨ ((((((p1 → False) ∧ (((p5 ∧ p4) → p3) → (p5 ∧ p5))) → p3) → p1) → (p2 → (p3 ∨ ((p2 ∧ (p1 → True)) ∧ True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588256234258119879393961854842 : (((((((p2 ∧ p3) ∧ (p3 ∨ (True ∧ p4))) ∧ ((True → (p5 ∨ (False ∧ ((p1 ∨ p2) → p3)))) → ((p3 → p1) ∧ False))) ∨ p3) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634832321682912503311652197959 : ((((((((p3 ∨ p4) ∧ True) → False) → ((True ∨ p2) ∧ (p3 ∨ (False ∨ (p2 ∧ (True → (True → p4))))))) ∨ (p4 → (p5 ∧ False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299191355814542930140133535580 : (False ∨ (((p5 ∧ ((((p4 ∧ (p5 ∧ False)) ∧ p5) → (p2 → ((p2 → (((p2 → False) ∨ p1) ∨ p2)) ∨ (False ∧ True)))) ∧ p4)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219148660722347254001326182203 : ((True ∨ (p4 → (p4 ∧ p1))) → (p5 → (p3 ∨ (True → (((p1 → (p2 ∨ (((p5 ∨ (p2 ∧ False)) ∨ (p1 ∨ False)) ∨ p5))) → p2) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262144832383386875907705439033 : (True ∧ (((((p5 ∨ (p4 → ((p4 ∨ p3) ∧ ((False → p3) → (((False ∧ True) ∧ p5) ∨ p1))))) ∧ ((p2 ∧ p1) → p1)) → p1) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156809300244912928888454682550 : (((False ∨ (p2 ∨ (((p4 ∨ p1) ∨ p1) ∧ (((p4 → ((p2 → p4) ∨ p5)) ∧ p1) ∧ p1)))) ∧ p3) ∨ (p3 → ((p5 ∨ True) ∨ (p3 ∧ p4)))) := by
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
theorem thm_5_vars_56934446531436460564065087264 : (((False ∨ (p5 ∧ p1)) ∧ (((((p5 ∧ p5) ∧ (True → False)) ∧ (p2 → ((p5 ∧ (p4 ∧ p1)) ∧ (False ∨ p3)))) → False) ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148298859112855373018058586069 : (((((p4 → (True ∧ p3)) ∨ p4) ∧ (True → (p4 ∨ ((p5 → (p3 ∨ True)) → p2)))) → (p3 → (p3 ∨ False))) ∨ (((True → p1) → p2) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164594013127542462671543447344 : ((((p5 → False) ∨ (((p5 ∧ (p4 ∨ p5)) ∧ p1) → (((p2 ∧ p4) ∧ p4) ∧ p4))) ∧ False) ∨ ((True ∧ p1) ∨ (True ∨ ((p4 ∧ p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358667385687008452911794476469 : (p5 → (p4 → ((((p5 ∧ p2) ∧ p4) ∨ (p4 ∧ p4)) ∧ ((((True → True) → ((True ∨ p1) ∧ False)) ∨ (p2 ∨ (p1 ∨ True))) ∧ (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64977015317162410087177235894 : ((p2 ∨ ((p1 → ((p1 ∧ p1) ∧ True)) ∧ (((((False ∧ p5) → True) ∨ (((p1 ∨ p3) → True) ∨ False)) → True) → ((p5 → False) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172125125397565737270774920900 : (((((((p5 ∧ p2) ∨ False) ∨ True) ∧ p3) ∨ (p3 ∧ p1)) ∧ (p5 → (p5 → p2))) ∨ (True → (((p4 ∨ False) → ((p4 ∧ p4) ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217698906780148319837034314254 : (((True ∧ (p3 ∧ p1)) → p5) → (((p4 ∧ (((p5 → p2) ∨ (p4 ∧ (True ∧ p5))) ∨ (p2 ∨ (p5 ∧ p1)))) ∨ True) ∧ (True ∨ (p5 ∧ p5)))) := by
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
theorem thm_5_vars_655645386588315396249992578815 : (((((((p3 → p4) ∧ (p5 ∨ ((p1 → (((True ∧ False) → False) ∨ p4)) ∨ (p4 ∨ p4)))) ∧ p5) ∧ (p4 → (p5 ∨ p1))) ∨ (True ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_160565904191538567691783469362 : (((((p5 ∧ False) ∧ ((True ∧ p3) ∧ p3)) ∨ ((p5 ∨ p1) → p2)) → ((True ∧ (p5 ∧ p1)) → p2)) → ((True → p4) ∨ ((True ∧ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337892221326161676206019598116 : (p1 → ((((p5 → (p3 → (p2 ∧ True))) → p4) ∨ (p3 ∨ (False ∧ (p5 → p1)))) → ((p2 → (p2 → False)) ∨ (((p2 ∨ p4) → p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245331750103576353667196397725 : ((p2 ∧ p2) ∨ (p1 → ((p3 ∨ (((p2 → p5) ∧ (p5 ∨ True)) ∨ p2)) ∨ (p4 → (p1 ∧ (((False ∨ p4) ∧ True) ∨ ((p2 ∧ True) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585760169790684055713432330 : ((((p4 ∧ (p4 → (p4 ∨ (True ∨ (p2 ∨ False))))) ∧ ((((p5 ∨ (True → p5)) ∨ ((p2 ∧ False) ∧ p5)) ∨ p4) → False)) → p3) ∨ p2) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 ∨ (True → p5)) ∨ ((p2 ∧ False) ∧ p5)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338405524710906731869259273584 : (p1 → (((False ∨ (p1 ∧ p1)) → p5) → ((True ∨ ((p5 → p1) → (p1 ∧ (True ∨ p2)))) → ((((p1 → False) ∨ True) → p2) ∨ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710000437362860774841187875167 : ((((((p2 ∧ p2) → (p5 ∨ p1)) ∧ True) ∧ ((p5 → (False ∧ (((False ∨ p5) ∨ (p2 ∧ (True → (True ∨ False)))) → (False ∧ p3)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53484504875235703234418621392 : (((p3 ∧ ((p5 ∧ p2) ∧ ((True ∨ True) → ((p4 ∨ p4) ∨ p2)))) → (p5 → (((((p5 → p3) → True) → True) → False) ∨ (False → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314225419792367586046467905681 : (p3 ∨ (((False ∧ ((((((p3 → (p4 ∨ p2)) ∨ p1) ∧ ((p1 ∨ True) ∧ p1)) ∧ False) ∧ p3) → (True ∧ p4))) ∧ p5) ∨ (p2 ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_735006367528506753140756667379 : ((((p3 ∨ True) ∧ ((p5 ∨ (p5 ∨ ((((p1 ∨ ((True ∨ p5) → (p3 ∧ (p3 ∧ (True ∨ (p5 ∨ p5)))))) → p4) ∧ p2) → p2))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117155432181533519415545422185 : ((True ∧ (((((p1 ∧ (p1 → False)) ∧ (((True ∧ p4) → p2) → (((False ∨ p3) → (p3 ∧ False)) ∧ p2))) ∧ p1) ∨ True) ∨ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791298747445339447236707066639 : (((True → ((((p2 → (((True ∨ (p4 ∧ p3)) ∧ p3) → p4)) → ((p3 ∨ p4) ∧ (False → ((True → False) ∧ (p4 ∨ p3))))) ∨ p4) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156973108581839776314753325535 : (((((p5 ∧ (p1 → p3)) ∧ ((p4 ∧ (False → True)) → p5)) → ((False ∧ (False → False)) ∨ p3)) ∨ p5) ∨ (((p3 → p2) ∨ (p4 → True)) ∧ True)) := by
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
theorem thm_5_vars_159524532178894674419625013804 : ((((p5 → p5) → ((p1 ∨ True) ∧ ((p1 ∨ ((True ∧ True) → (p2 → p1))) → (p3 ∨ p3)))) ∧ True) → ((True → p1) → ((p5 ∧ p4) → p3))) := by
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
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (p1 ∨ ((True ∧ True) → (p2 → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118097781439059738622087655357 : ((False ∨ ((p4 ∨ ((p4 ∨ p3) ∧ ((p2 ∧ ((False ∧ p3) → (False → ((p3 → p4) ∧ p2)))) ∧ (True → (p2 ∨ p1))))) ∧ False)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158337218228511983909379616330 : (((p1 ∧ p5) ∧ (p1 ∧ ((p1 → ((p1 ∨ p5) → p1)) ∧ (p2 → (True ∧ (p4 ∨ (p1 → p1))))))) ∨ (((p3 ∨ (False → p5)) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_315400441028243029739362350409 : (p3 ∨ (((p4 ∧ p4) ∨ p4) ∨ ((False ∨ True) ∨ ((((p4 ∨ True) ∨ p4) ∧ (((False → ((p4 ∨ (p1 ∨ True)) → False)) ∧ p4) → p4)) → False)))) := by
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
theorem thm_5_vars_324667375852352993803210131215 : (p5 ∨ ((False ∧ (p2 ∧ p4)) ∨ (((p4 ∨ (False ∧ ((False ∨ (False → True)) ∨ (p5 ∧ (p4 → p4))))) ∨ p5) ∨ (True ∧ ((p2 ∨ p5) → True))))) := by
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
theorem thm_5_vars_631050522337748631746295853045 : (((((((p3 ∧ (((True → p4) → ((False ∨ ((False ∨ p1) ∧ (True → True))) ∨ p1)) ∧ p3)) ∧ ((True → p1) → False)) ∨ p2) → p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143863419798097717538065301159 : (((((True ∧ (p4 ∨ (p1 → p5))) ∧ (p1 ∧ (p5 → (p1 ∧ ((p3 ∨ p4) → p5))))) ∨ (p1 ∨ p4)) ∨ True) ∧ (((p3 → True) ∧ p4) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640148642978015306626885558304 : ((((((p5 ∨ p4) ∨ p5) → ((p5 ∧ p2) ∨ ((False ∨ (p5 ∨ (((False → True) ∧ p3) ∧ (True ∨ (p5 ∨ (p3 ∧ p5)))))) ∧ p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140623110330858251767120908399 : (((p1 ∧ (((False ∧ (((True ∨ (True ∧ p2)) ∨ p5) ∨ True)) → p3) ∨ (p1 ∨ False))) → (False ∧ (p4 → (p5 → p4)))) → ((p3 ∨ p1) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∧ (((False ∧ (((True ∨ (True ∧ p2)) ∨ p5) ∨ True)) → p3) ∨ (p1 ∨ False))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111244437507295449396163612697 : ((((p3 → False) ∧ ((p3 ∨ (p5 ∨ ((p3 → (True ∨ (p2 ∨ (((p3 → p4) ∧ False) ∧ p5)))) ∧ (p1 ∨ p4)))) ∧ False)) ∧ False) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61569565517938602357585365650 : ((p1 ∧ ((((p3 ∨ p4) ∧ (p1 ∧ p2)) → p5) → (((p4 ∧ (p1 → (p1 → p3))) → (p3 ∨ (p4 → p2))) ∨ ((p4 ∨ p5) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309789881338098789536308135736 : (p2 ∨ (((p1 → (p4 ∨ (((p5 ∨ p5) ∨ (False ∨ (((p4 ∨ (p4 → True)) → p3) ∧ p3))) → p1))) → p5) ∨ (((p3 ∨ p5) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308418120730253933479883019287 : (p2 ∨ ((((((((p2 → (p5 → (True ∨ (p4 ∧ False)))) → False) ∧ (True ∨ (p2 → p3))) ∧ (p4 → p3)) ∨ True) ∨ (p4 ∨ p4)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206391315271969455500269868940 : ((p3 ∨ ((p1 ∧ (p4 → p4)) ∨ p5)) ∨ (True ∧ (((((((p4 ∧ p2) ∨ p5) ∨ p1) → p1) ∧ (p3 → True)) ∨ p5) ∨ ((p3 ∨ p5) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615870647459695651767394200683 : (((((((p4 → p5) → True) → ((p3 ∧ p1) ∨ (p2 → ((False ∨ p4) ∧ p3)))) ∨ (False ∨ ((p2 → (False ∨ (p3 ∧ False))) ∨ p2))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137998189683377403941984277784 : ((p5 ∨ (p3 ∨ (((p1 → p4) ∨ (((p5 ∨ p3) → p1) ∧ (p4 ∧ p4))) → ((p5 ∧ p1) ∧ (p3 → (p2 ∧ p1)))))) ∨ (p4 → (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672961726410458086771172203193 : (((((((p4 ∧ ((p1 ∨ p2) → p3)) ∧ p3) → ((p1 ∧ p3) ∧ (p1 ∧ p4))) ∧ ((p1 ∨ False) ∨ (False → False))) → ((p2 ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873388529643134495720859143 : ((True → ((p4 ∨ ((True ∧ True) → ((p4 ∧ (p2 ∨ p2)) ∨ (((p2 → False) ∨ True) ∨ (((p1 ∧ False) → p2) ∧ p4))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247984172655628529616298698360 : ((p1 ∨ p4) ∨ (((p5 ∨ p2) ∧ p4) ∨ (((p2 ∨ (p2 ∨ ((p5 → ((p1 ∨ p4) ∧ ((p2 ∧ False) ∧ p5))) → (p5 ∨ True)))) ∨ p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_69165288372931803530024715172 : ((p5 → ((p5 → (((False ∧ (p5 ∨ ((True ∧ p5) ∨ ((p1 → p2) → p3)))) → False) ∧ (p1 ∨ p5))) → (p2 ∨ ((p3 ∨ True) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_165563151379378666632202188699 : ((((((p3 ∨ p2) ∨ (p5 → False)) ∧ p3) ∧ True) ∨ ((p3 ∧ (p4 → (False ∧ p2))) ∨ p2)) ∨ ((p2 → False) ∨ ((p3 ∧ True) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_48849410794646284023989221112 : (((p2 ∨ (((p3 ∧ True) ∧ ((p3 → (p1 ∧ ((False ∧ (True ∧ p4)) ∨ p2))) ∨ (p2 → True))) ∨ (True ∨ p2))) ∧ ((p5 ∨ False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175402231602172642221729965412 : ((False → ((True ∨ (False → ((((p5 ∨ p4) ∧ p1) ∧ (p5 ∨ p2)) ∧ True))) ∨ p4)) → ((p1 ∨ p1) → (False ∨ (p1 ∨ (p5 ∧ (p1 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759072495540011297116927628705 : (((p2 ∧ ((p4 → ((False ∨ p2) → ((((((p1 ∨ True) ∧ (p1 ∨ (p5 → True))) → (True → p1)) → p3) ∧ (False ∨ True)) ∧ p4))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263140393898684789092806324484 : (True ∧ (((p5 ∨ (False ∨ p5)) → ((False ∧ ((((p2 ∨ ((False ∧ True) → p1)) ∨ (True ∨ False)) ∨ (True ∨ p2)) ∧ p4)) ∨ True)) ∨ (p1 ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_213874568320229702428977419238 : (((p2 ∨ (p3 ∧ p2)) ∨ p3) ∨ ((p4 ∨ True) → (p1 → ((True ∧ p4) ∨ (False ∨ ((p4 → p1) ∧ ((p5 ∨ (p1 → (p5 → p1))) ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206245481728146449209391014734 : ((False ∨ ((p5 ∧ (True → p5)) ∧ False)) ∨ ((p2 ∧ p2) ∨ ((p2 → ((p1 ∨ ((p2 ∧ p4) ∧ False)) → ((p3 → (False ∧ True)) ∧ p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97053433509366636041706913830 : ((p1 ∨ (True → ((p2 ∧ ((((p5 ∧ True) → (p3 ∨ ((((p1 → p5) ∧ p1) ∨ p5) ∨ p5))) → (p2 → (True ∧ p2))) ∧ False)) ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178963776952614986323468128492 : (((p2 ∨ p3) ∨ (((p3 → ((True → (p1 ∨ p4)) ∧ p3)) ∨ p3) ∨ False)) ∨ (False → (((p5 ∧ True) ∨ ((p2 ∨ p4) ∨ p3)) ∨ (p4 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626381448800217190559596463731 : ((((p3 → (p2 → (((False → (((False ∧ True) → (p5 → (p3 → False))) → False)) ∨ p2) → (p4 ∧ (False ∨ ((True → False) → p5)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_227668032793947646728570197551 : ((False ∧ (p2 → p3)) ∨ (p2 ∨ (((((p5 ∧ False) → ((False → (p2 → True)) ∨ p3)) → (p4 ∧ False)) ∨ (True → p2)) ∨ ((p4 → True) ∨ p4)))) := by
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
theorem thm_5_vars_254876223951249962235193205121 : ((p4 ∧ True) → (((((True → p3) ∨ ((p3 ∨ True) → (False ∨ (p2 ∧ (((p2 ∨ True) → (p5 → p3)) ∧ p3))))) ∨ (p5 ∧ p1)) ∨ False) ∨ p4)) := by
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
theorem thm_5_vars_65849205252540966248725086986 : ((p4 ∨ (((p2 ∧ p5) ∧ p2) → (((p3 ∨ ((p2 ∨ (p5 ∧ True)) ∧ ((p5 ∨ p1) ∨ (p1 → False)))) → (p2 → False)) ∨ (p5 → p5)))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224834565193468483835289085705 : ((p4 → (p2 → p4)) ∧ (((p3 ∨ (p4 → p3)) ∧ p4) → ((((((p1 → (True ∨ p4)) ∧ False) ∨ p1) → p3) ∧ p4) ∧ ((p2 ∨ p5) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h3.left
  let h16 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the left can always be decomposed.
  let h19 := h3.left
  let h20 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46768156899518901258967043146 : (((p3 → (((p3 → (((True ∧ p5) ∧ (p1 ∨ (p4 ∧ p2))) → ((True → False) ∧ False))) ∧ (False → (True → p1))) ∨ p4)) ∧ (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246168645602574896716203822348 : ((p4 ∧ p2) ∨ ((p5 → p1) → (p3 ∨ ((True ∧ (True → p2)) → (((p5 → (True ∧ p2)) → (True ∧ (p4 ∨ ((False → p2) ∧ p2)))) ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205801962150317161680722352836 : (((p2 ∨ p2) → ((False ∨ p4) ∨ p3)) ∨ (False ∨ ((((True → (p1 ∧ (p3 ∨ p3))) ∧ ((p1 ∧ p3) ∨ p3)) → (p1 → (True → p1))) ∧ True))) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310530757435110251228907262598 : (p2 ∨ ((((p1 ∨ p3) ∨ (True ∨ p1)) → False) → (True → ((p1 ∧ ((p2 ∧ (p2 ∨ ((p3 ∧ True) ∧ (p4 ∨ p4)))) ∨ p5)) → (p4 ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((p1 ∨ p3) ∨ (True ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h20 : ((p1 ∨ p3) ∨ (True ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350244129702142186258313266442 : (p4 → ((True ∧ (((((p5 ∧ (False ∨ p1)) → (False ∧ p3)) ∧ (p3 ∧ False)) ∧ (False ∨ False)) ∧ ((p1 ∨ p3) ∨ ((p5 ∧ True) ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8093076697914631355791180469 : (((((p4 ∧ ((True ∨ p1) ∧ True)) ∧ (p5 ∧ ((p5 ∨ (True ∨ True)) ∧ (p2 → ((p5 ∨ p5) ∧ (p5 ∧ (p1 ∧ p1))))))) ∨ True) ∨ p2) ∧ True) := by
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



