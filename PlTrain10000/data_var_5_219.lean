variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344176341332691198575147799337 : (p2 → (p1 ∨ ((((p3 ∨ (((p4 → (p4 → ((p2 ∧ False) ∨ False))) → p4) → (p1 ∨ ((p1 → p3) ∨ False)))) ∨ p1) ∨ p2) ∨ (p4 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347046096029122865812565287328 : (p3 → ((((p1 → p5) ∧ ((p4 ∧ p1) → (p2 ∧ p5))) ∧ ((p1 → p5) ∧ (p3 ∨ p5))) → (p4 → (True ∧ (p2 ∨ (p3 → (p4 ∨ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607251022847933051830331678085 : (((((((True → (p5 ∨ p4)) → p3) → ((((True ∨ p3) ∨ ((p3 ∧ ((p1 ∧ (p2 ∨ p3)) ∨ True)) ∧ p1)) → True) → False)) ∧ p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_158466392959630212398434888959 : (((p2 → p4) ∨ (((p1 ∨ p5) → ((False ∨ False) ∨ (p2 ∨ True))) ∨ ((p1 ∨ False) ∧ (p1 ∨ p2)))) ∨ (((p4 → p1) → True) → (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319671056656134550853465092661 : (p4 ∨ (((((True → p3) → p1) → True) ∨ (False ∧ p3)) → ((p3 ∨ ((((p2 → p5) → p3) → p4) ∧ True)) ∨ (False → (p5 ∨ (p1 ∧ p1)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301412787074433690453787953672 : (False ∨ ((((p1 ∧ False) → p4) ∨ p3) → ((((p4 ∨ p4) ∧ p1) → (((((p4 → p4) ∨ p4) ∨ (p2 → (False ∨ p4))) ∧ p5) ∨ p1)) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166765708993951509624928987345 : ((p5 → ((True → (((p3 → (False ∨ p2)) ∨ ((p4 → p1) ∧ False)) ∧ (p2 ∧ p2))) ∧ False)) ∨ (((p3 → (True → (p2 ∧ p2))) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113102538962906374992369220346 : (((True → ((((((p4 ∨ True) → (p1 ∧ p1)) → p2) ∧ (p5 ∨ (p2 ∨ (True ∨ True)))) → p2) ∧ ((p4 ∧ False) ∨ False))) → p1) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41669602972852380040370749334 : (((((p1 ∧ (p4 ∨ (False → p5))) ∨ p1) ∨ ((p1 ∧ p2) → ((((False ∨ (p5 ∨ p5)) ∨ p3) ∧ (p4 ∧ p5)) ∧ (p3 ∧ True)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194660157512380120383777926902 : (((((p2 ∧ p2) ∨ p3) ∨ (p2 → p5)) ∨ True) ∧ ((p1 ∨ p3) ∨ (p4 ∨ ((p1 → (((p2 ∧ (False ∧ p3)) ∧ (p3 ∨ p5)) → p3)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258791382794278304807395988849 : ((True → False) → (((p2 ∧ (False ∨ p2)) → p2) ∧ (((p5 → False) ∨ True) → ((p2 ∧ (True ∧ p2)) ∧ ((p3 ∨ p2) → ((p2 ∨ p5) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136936259980649816440246412565 : (((p3 → p4) ∨ ((True ∧ (p1 ∨ (p5 ∧ ((p4 ∨ False) ∧ True)))) ∨ (True ∧ ((False ∧ ((p5 ∨ False) ∨ p3)) ∧ True)))) ∨ (p5 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750929160451468388017988728046 : (((True ∧ ((((False ∧ False) → p2) ∧ ((p5 ∧ p3) ∧ p5)) → (p1 ∨ ((True → (((p4 ∧ True) ∨ ((p4 ∨ p2) ∨ p4)) ∨ True)) ∨ p1)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793684047793406853202964404343 : (((True → (p5 ∨ (p5 → (True ∧ (p3 ∨ (p1 ∧ (p3 ∨ ((((p1 ∧ ((((False ∧ p4) → p3) ∧ p4) → p1)) ∨ p4) ∨ False) → p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260344210085983774179466630586 : ((p2 → p5) → (((p2 → ((p2 ∧ (p1 ∨ True)) ∨ (p2 ∨ False))) → (p3 ∧ (((p5 ∨ ((p1 ∧ p4) → p2)) → (True ∨ True)) → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619795022546729527367005201303 : (((((p1 ∨ p5) ∧ ((p2 ∧ p3) ∧ ((((True ∧ p3) ∨ (((p3 ∨ False) ∧ p1) ∧ ((p1 ∧ (p3 → False)) → p3))) ∧ p5) ∨ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764902120167819897086874167929 : (((p4 ∧ ((((p5 ∧ (p3 ∨ False)) → (p1 ∧ False)) ∧ ((p1 → p5) ∨ ((True ∧ ((p1 → (False ∨ (p4 ∨ p4))) ∨ False)) → p1))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860227468189495814015072660867 : (((((p4 ∧ ((True → (((p3 ∨ p5) ∨ ((True ∨ p2) ∨ False)) → (p1 → ((p5 ∧ True) ∨ p3)))) → (p4 → p1))) ∨ (p5 ∨ True)) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ ((True → (((p3 ∨ p5) ∨ ((True ∨ p2) ∨ False)) → (p1 → ((p5 ∧ True) ∨ p3)))) → (p4 → p1))) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_156977589290662997072500375731 : ((((p1 → (((p1 ∨ (p4 ∧ p3)) → p5) → False)) ∧ ((p1 ∨ (p5 ∨ False)) ∨ (p4 ∧ p5))) ∨ True) ∨ (((False ∧ p4) ∧ True) ∧ (p4 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717351688950067050991181989457 : ((((p5 ∨ (p4 ∨ (p2 → p3))) ∧ (p2 ∧ ((p2 ∨ False) ∧ (((((p5 ∨ p4) → True) ∨ (p4 → p3)) → ((p3 → p4) ∧ False)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320368602802917036808354871628 : (p4 ∨ ((p4 → p1) ∨ (((False ∨ p2) ∧ (((True → False) ∧ p3) ∨ (True → False))) → (((((False ∧ p1) ∧ p4) ∨ (p5 → True)) ∧ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50711457916204178915502359980 : ((((True ∧ p1) ∨ (((((p5 ∨ (False → False)) ∨ (p1 ∨ (False ∨ (p2 ∨ False)))) ∧ p5) ∨ True) ∨ p3)) → ((p1 ∨ (p5 ∧ p4)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53966332754255630602094088510 : (((((True ∨ p4) ∧ (p1 → ((p2 ∨ p4) → False))) ∧ p3) → (p5 ∧ (p4 → ((p4 ∨ (p3 → (((p3 ∨ p5) ∨ True) ∧ p4))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44548454694981032532946180931 : (((((((False ∧ False) ∨ (True ∨ p2)) ∧ p3) ∧ p5) ∧ (((((False ∨ False) ∨ ((p1 ∧ True) → p4)) ∨ (True ∨ p1)) → False) ∧ p5)) → p1) ∨ False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : (((False ∨ False) ∨ ((p1 ∧ True) → p4)) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h20 : (((False ∨ False) ∨ ((p1 ∧ True) → p4)) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h20
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185026008564602227154935177809 : (((p4 ∨ p5) ∧ (((True ∧ False) → (True ∧ (p5 ∧ p1))) ∧ True)) ∨ (True → ((((p5 ∨ True) ∨ (p3 → False)) → p4) ∨ (p3 → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230770835659098265108463715041 : (((True ∧ p1) ∨ p2) → ((((p2 ∨ p5) ∧ ((p5 ∧ (p3 ∧ (True ∨ ((p2 ∨ False) ∧ p3)))) ∨ p3)) ∧ p2) ∨ (((p5 → p2) ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59920152399835737110372580981 : (((p5 ∧ p4) → (((False ∧ (p4 ∨ ((p5 ∧ (p1 ∨ (p5 → p4))) ∨ p4))) ∨ (p2 ∧ False)) ∧ (((p2 → p2) ∧ False) ∨ (p3 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612753773923692965504716142311 : ((((((p5 → ((p4 → True) → False)) ∨ (((False ∨ p1) ∧ (((p5 ∧ True) → (p4 → True)) ∧ p1)) → (p3 → p2))) ∨ (False → False)) ∨ p5) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_190090716693835877995213354252 : ((((((p3 ∨ p2) ∨ p1) ∧ p4) ∨ (True ∨ p5)) ∧ p2) ∨ (p5 ∨ (p4 → ((False ∧ p5) → ((p3 ∧ p1) ∧ (True ∨ (p2 ∨ (p4 ∧ False)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353531533518493178774278724479 : (p4 → (p3 ∨ (((((((((((p1 ∨ p5) ∨ (p1 → True)) ∧ p2) ∧ True) → True) → ((p5 ∧ True) → p3)) ∨ p4) → True) → p5) ∨ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148273196651457488812547708813 : (((((((p1 ∨ p3) → p3) → True) ∧ (p3 ∧ ((True → p5) → (p1 ∧ True)))) ∧ p4) → ((p1 ∨ p5) ∨ p4)) ∨ ((p1 ∧ p5) ∧ (False ∧ p2))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168335297038442046652458155908 : (((True ∧ False) ∨ ((((p1 ∧ p4) → (p5 ∨ (p1 ∨ p4))) ∨ (p2 ∧ (p1 ∨ True))) → False)) → (p1 ∨ (p4 ∨ (((p2 → p5) → p2) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p1 ∧ p4) → (p5 ∨ (p1 ∨ p4))) ∨ (p2 ∧ (p1 ∨ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116361364284250177239304495716 : ((((p5 → p3) ∨ p1) → (((((p2 → (p1 → p4)) ∨ True) ∧ (p3 → ((p4 ∨ False) ∧ True))) ∨ (p3 ∨ p2)) ∨ (True → p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626534066684307266583034209014 : ((((p4 → (((((p3 → True) ∨ False) ∧ (p3 ∧ p3)) ∨ (p1 ∨ p1)) → ((p3 ∨ p5) ∨ ((p2 ∧ True) ∨ ((p2 ∧ p1) → p1))))) ∨ p3) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736462766343659303685990843912 : ((((p1 → p1) ∧ ((True → (((((p4 → True) ∨ ((p4 ∧ (((p1 ∧ False) → p2) ∨ p3)) → p3)) ∧ (p5 ∨ p4)) → p1) ∨ p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634802950888234090708519829566 : ((((((((p3 → (p2 ∨ (p2 ∨ False))) ∨ True) ∧ (p5 ∨ p1)) → (p4 → ((p1 ∨ (True ∧ p2)) ∨ p1))) ∨ ((p5 → p2) ∧ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346772692682380403082152615243 : (p3 → ((((p5 → (p1 ∨ p2)) ∧ ((((p4 → ((p3 → p1) ∧ p5)) ∧ p1) ∧ (p2 → p2)) ∨ p3)) → p2) ∨ ((p1 → p5) → (p4 ∨ p3)))) := by
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
theorem thm_5_vars_720380849398794977696741341463 : ((((((True ∨ p5) → p1) ∨ True) → (p5 ∨ ((p1 ∧ ((p2 → ((False → (False → True)) ∧ p5)) ∨ p3)) → ((p3 → p1) ∨ (p4 → p1))))) ∨ False) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180426000040577069515746684920 : ((((p5 → (((p5 ∨ p2) → p5) → (False ∧ p3))) ∨ True) → (p5 → p2)) → ((((p4 ∧ p1) → (p3 ∨ p2)) → (p5 → p3)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60552867713228668896469289246 : ((True ∧ ((p1 ∨ (p2 ∨ (p2 ∨ ((((((p3 → p3) ∧ (p5 ∧ p2)) → p5) ∧ ((True ∨ p4) → p1)) ∧ (p1 → True)) → p2)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136504578931753091459141682564 : (((False ∧ (True → p5)) ∧ ((p1 ∧ (p3 ∧ False)) ∨ (((((((False ∧ p3) ∧ p1) ∧ p2) → p4) ∧ p2) ∨ p2) ∨ True))) ∨ (True ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608820859766994976906315189945 : ((((((p5 ∨ (((p2 ∨ p5) ∧ p1) → ((p4 ∨ False) ∧ ((p5 → p4) → ((p5 ∨ p1) ∧ p4))))) → ((p5 ∨ p5) ∨ p4)) ∨ p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45650597054560890149044387226 : (((p4 ∨ (p5 ∧ (((((False ∧ p3) ∧ False) ∧ (False ∨ (True → ((p2 ∨ True) ∧ ((p3 ∨ False) ∨ False))))) ∨ p2) → (p1 ∨ p5)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184151761282998976545236364015 : (((p1 ∨ ((p4 ∧ p4) → ((p2 ∧ p5) ∨ (p5 ∨ p5)))) ∨ p5) ∨ (((p4 ∨ (p5 ∨ (((True ∧ p5) → p1) → p4))) → p4) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312433248788447094997995159054 : (p2 ∨ (p4 → ((((p5 ∧ (p3 ∧ (p5 ∨ (True ∧ (p2 ∧ False))))) ∨ p5) ∨ p4) ∨ ((((p4 ∨ p4) → (p3 → (p2 ∧ False))) ∨ p1) → p4)))) := by
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
theorem thm_5_vars_208535585507919431951161495024 : (((False ∨ p1) → ((True ∧ True) ∧ p3)) → (((((p2 ∨ ((False ∨ p2) → (p5 ∨ ((True ∧ p4) → True)))) ∨ p5) ∧ p4) → False) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2663388054636161570703931976 : (((True → False) ∨ (p3 ∨ (p1 ∧ p4))) ∨ (False ∨ ((p4 ∧ True) ∨ ((True ∨ ((False ∧ True) ∨ (False → (p2 ∧ True)))) ∨ (p1 ∧ p1))))) := by
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
theorem thm_5_vars_137048359323686452269021320633 : (((False → p4) → (((((p2 ∧ p3) ∧ (False ∨ p1)) → p5) ∧ (p2 ∨ False)) ∨ (p4 ∧ ((p5 ∧ (p4 ∨ True)) ∧ True)))) ∨ ((p5 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7480526060181234394952029461 : (((p1 → ((((p5 ∧ p1) ∨ ((p5 ∧ False) → p3)) ∨ ((p3 ∧ p1) ∧ (p2 ∨ (False ∧ True)))) → ((True ∧ (False ∨ False)) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585435781983936090976102630779 : ((((((False ∨ (p3 → (((True ∧ ((False ∨ (p4 ∧ False)) ∨ (False ∨ p4))) ∧ (p3 ∧ ((p3 ∧ p3) ∨ p5))) ∧ p2))) ∧ p2) ∧ p5) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670082000543092186107412616584 : (((((((p4 ∨ (True → False)) ∨ p1) ∧ p1) ∧ ((p5 ∨ (True ∨ p4)) ∨ ((False ∨ (p5 → (p4 ∧ p4))) ∧ p3))) ∨ ((p3 → p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173253159533924733282766000259 : ((True → (p2 → (p5 ∧ ((p4 ∨ p2) → ((p4 → ((p1 ∨ True) ∨ p2)) ∨ p1))))) ∨ (False ∨ ((((p2 → True) ∧ False) ∨ (p3 ∨ True)) ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183107688617276413654308733670 : (((p3 ∨ p2) → (False ∨ (((False ∨ (p3 ∧ True)) ∨ True) ∨ p1))) ∧ ((False ∨ True) ∨ (((False ∨ (True → False)) → (True ∧ p1)) → (False → False)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_607291051193247560448750238553 : ((((((p2 → (p5 → p3)) ∧ (((p3 ∧ (p1 → p3)) → ((p1 → False) → ((p3 ∨ p5) ∨ p5))) ∧ ((p4 ∨ p1) ∧ p4))) ∧ p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707081580792229020514886051484 : ((((((((p3 ∨ p2) ∨ p1) → True) ∨ False) → False) ∨ (((True ∨ p3) ∨ ((((p2 → p1) ∧ p1) → (p1 ∧ (p5 ∨ p4))) ∧ p3)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60617571446885333970803973345 : ((True ∧ ((p2 ∧ (p1 ∨ ((((False → (p2 ∧ (p2 ∧ (p1 ∨ (True ∨ (p3 ∧ (p5 ∨ True))))))) ∧ p2) ∧ p4) ∨ p1))) ∨ (True ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44074701298209719077217428739 : (((((p3 → ((((((p2 ∨ p4) ∨ p1) ∧ False) ∨ False) ∨ p1) ∧ False)) ∨ (((p4 ∨ p3) ∧ p5) → True)) ∧ ((p2 ∧ True) ∨ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51155435035689342464667846524 : ((((True ∨ (((False ∧ False) ∨ p5) → ((p3 ∨ p1) ∧ (p2 ∨ ((False → p3) ∨ True))))) → False) ∨ (p5 → (False → (p3 ∨ (p1 ∧ False))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3323987379124380808597766055 : ((p4 ∧ p4) → (False ∨ (p1 ∨ (((False ∨ ((((p1 ∧ (p3 → p2)) → p3) → (p1 → p3)) ∨ (p1 ∧ p3))) ∧ (False ∨ p3)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215142927408985447365700769163 : (((p5 → p1) → (False ∧ p4)) ∨ ((False ∧ (((p3 → p1) → (True ∧ (p3 ∨ p4))) ∨ p2)) ∨ (True ∨ ((p2 → (p5 ∨ p5)) ∨ (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163752742159251333309902884273 : (((p4 → True) → ((True → (((((p4 → p2) → p4) ∨ p1) ∧ False) ∧ p1)) → (p4 ∨ p5))) ∧ (p3 ∨ (p1 ∨ (True ∨ ((True ∧ p5) ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166398742851849364863487986219 : ((False ∨ (p4 ∧ (((p5 ∧ True) → (p5 → p3)) ∧ (((p5 → p4) ∧ (p3 ∧ p3)) ∨ p2)))) ∨ (True ∧ ((((p4 ∨ p3) ∨ True) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943699337548731329251654135531 : ((((p1 ∨ (p4 ∧ (p3 → False))) ∧ ((p4 ∨ (p1 ∨ ((p3 ∧ (p2 → True)) ∧ ((True → p5) ∨ False)))) ∧ (p3 ∧ ((True → True) ∨ p4)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h6.left
        let h15 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h6.left
          let h25 := h6.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h27 =>
            -- One of the premise coincides with the conclusion.
            exact h4
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h3.left
    let h33 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h38 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h39 := h31 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h41 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h42 := h31 h41
        -- False on the left can always be used.
        apply False.elim h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h33.left
        let h46 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- One of the premise coincides with the conclusion.
          exact h44
        case inr h48 =>
          -- One of the premise coincides with the conclusion.
          exact h44
      case inr h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Conjunctions on the left can always be decomposed.
        let h52 := h50.left
        let h53 := h50.right
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h54 =>
          -- Conjunctions on the left can always be decomposed.
          let h55 := h33.left
          let h56 := h33.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h57 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h58 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h59 := h31 h58
            -- False on the left can always be used.
            apply False.elim h59
          case inr h60 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h61 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h62 := h31 h61
            -- False on the left can always be used.
            apply False.elim h62
        case inr h63 =>
          -- False on the left can always be used.
          apply False.elim h63
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655094400759449191495780119378 : (((((False ∨ (p1 → (((((p5 ∧ (p5 ∧ p2)) → False) ∨ ((p4 ∨ p3) ∧ p3)) → ((True ∨ p4) → True)) ∧ p3))) → False) ∨ (True ∨ p2)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_111570865174229098293690286036 : ((((((p2 ∨ p5) → p4) → (p1 ∧ ((((p1 ∨ p2) ∨ (p4 → False)) → p5) ∨ (True → ((p5 ∧ p4) ∧ p4))))) ∧ p4) ∨ True) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253015962883593388313354017756 : ((True ∧ p3) → ((((p4 → (p2 ∧ (p1 ∨ ((True ∧ (p3 ∨ p4)) → p5)))) ∨ p3) ∨ p4) → ((p5 ∧ p3) → (p2 → ((True ∨ p4) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h17 := h3.left
  let h18 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h1.left
    let h28 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340956960823492231336098850436 : (p2 → ((((True → True) ∧ True) → ((p5 → (((((p5 → p1) ∨ ((True ∨ (p5 ∧ False)) ∨ True)) → p3) ∨ (p1 ∨ True)) ∨ p3)) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695079446654820905237078793421 : (((((((p4 → (p1 ∨ ((p5 ∧ p1) ∧ (p5 ∧ p4)))) ∨ p4) ∧ p5) ∨ p3) → ((p2 → ((p2 → (False ∧ (p5 → True))) ∨ p4)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765274443184855289029026862900 : (((p4 ∧ ((((p3 → ((p2 ∨ (True → (True ∨ p2))) ∧ p1)) ∨ ((p3 ∧ False) ∨ (p3 ∨ True))) ∨ (False ∨ p1)) ∧ ((p1 ∨ True) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165856155373395862250063451431 : (((p2 ∧ (p4 ∧ p3)) ∨ (p1 ∧ ((True ∧ ((True → (p3 → True)) ∨ (p2 → p2))) → p1))) ∨ (((p2 ∨ (p2 ∧ p3)) → (p3 → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343381642691270996099212227505 : (p2 → ((False ∧ False) ∨ ((((((p1 ∨ (True ∨ ((p2 ∨ p4) ∧ (p5 ∨ p4)))) → p1) ∨ (p5 ∧ p2)) ∨ p1) ∨ (p3 → p2)) ∧ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63414071411849794246342716873 : ((p5 ∧ (p5 ∨ (((p1 ∧ True) ∧ (p5 → p2)) → (((False ∧ (True → p2)) ∧ True) ∨ ((False ∨ (True → ((p4 ∧ p5) ∨ p2))) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187256312360606981414747535644 : ((True ∧ (p4 ∧ ((True → False) ∨ ((p5 ∨ (False ∨ p2)) ∨ p5)))) → (((True → ((False ∨ True) ∧ False)) ∧ p4) → (((p5 ∧ False) ∧ p5) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731369365782919294674762748558 : ((((p5 ∨ (p4 ∧ p5)) → ((p2 ∧ (p4 ∧ ((p2 → p5) ∧ (p4 ∧ (False ∧ (p2 ∨ ((p1 ∨ p2) → p2))))))) ∨ ((p3 ∨ False) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208638924245770508946133497754 : ((True ∧ ((False → p4) ∨ (p1 ∧ p3))) → (p3 → ((False ∧ ((True ∨ (((p3 ∨ (((p1 ∨ p2) → True) → p5)) ∨ p2) ∧ p5)) → p1)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337950233594389823415149248682 : (p1 → (((p2 ∧ (p4 ∨ (p5 ∧ (p5 ∨ p3)))) ∨ (p5 ∧ (p1 ∨ False))) ∨ (((p4 → (((p3 ∨ (True → False)) → p1) ∨ p5)) → False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (((p3 ∨ (True → False)) → p1) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136279852332951558239745500031 : ((((p1 ∧ p3) ∧ ((p3 ∧ p5) → True)) → ((p3 → ((False → (p5 ∧ p2)) ∨ (p5 ∧ (True → (p5 → p5))))) → p4)) ∨ ((False → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48435736423246232264427174987 : (((p4 → (((((p5 → ((False ∧ (p4 ∧ p3)) ∧ p4)) → (p5 ∧ False)) ∧ p5) → p5) → (p3 ∧ (p3 ∨ (p1 ∨ True))))) → (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204104560229778310857362906893 : (((((False ∨ p3) ∧ p3) ∧ p4) ∧ p2) ∨ (((p4 ∨ True) ∧ p4) → ((p1 ∧ True) ∨ (p4 → (((True ∨ (p4 ∨ (True ∨ False))) ∨ False) → True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260983437258203790018259798365 : ((p4 → p1) → ((p4 → True) ∧ ((((True ∧ (p2 ∧ ((p5 ∨ (p4 ∨ ((p2 ∧ p3) → p2))) ∧ (True → p1)))) → p5) ∧ p1) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157691446311538161669852518506 : (((p4 → (((p3 → (p5 → (p4 ∧ (True → True)))) → (p1 → p3)) ∧ p4)) ∨ ((p2 ∨ False) ∨ True)) ∨ ((p3 → p4) ∨ (p4 ∨ (False ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115759585877973256300202565395 : (((False ∨ ((p4 ∨ (p5 ∨ p1)) ∧ p4)) → (((((((p4 ∨ p2) ∧ p2) ∧ False) ∧ p2) ∨ p1) → p1) ∧ ((p2 ∧ False) ∨ p5))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137958531052353369552925217579 : ((p5 ∨ ((p4 ∨ (p2 ∨ (p1 ∧ (((False ∨ True) → p2) → ((((p1 ∧ True) → (p2 → p3)) → p1) → p5))))) → p5)) ∨ ((False → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311248186520339646129016476669 : (p2 ∨ ((p5 → p3) → (p3 → ((((((p5 ∨ (p3 ∨ p1)) ∧ (p3 ∧ p2)) ∧ (p4 ∧ (p3 ∨ p4))) ∨ (p5 ∨ True)) ∧ (p3 ∧ p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638138535932386082882598351825 : (((((((p3 ∨ (p2 → True)) ∨ (p2 ∨ p4)) ∨ p5) → ((((p4 ∨ p4) ∧ (False ∨ (p2 → (False ∨ p4)))) ∧ (p1 → p5)) ∨ p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48371466377420406985467185679 : (((p5 ∨ ((p1 → (p1 → p5)) ∧ (((True → True) → True) ∧ ((((((p2 → p2) ∧ p5) → True) → p1) → p4) ∨ True)))) → (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180444060746858787907850873947 : ((((p1 → (p2 ∧ (p3 ∨ p4))) → ((p1 → False) ∨ p2)) → (p5 ∧ True)) → (p2 ∨ ((((((p2 ∧ p2) → p1) → False) ∨ True) → True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775991794714087874980227701685 : (((False ∨ (p3 → (((False → (((True → ((((p3 ∧ (p5 → ((p5 ∨ p5) → p2))) ∧ p2) ∨ p3) ∧ p5)) ∧ p5) → p2)) → False) ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351536659087203967756725540024 : (p4 → ((((p3 ∨ p3) ∨ p2) ∧ (((p3 → p2) ∨ ((p3 ∨ p5) → ((True → True) ∨ p1))) ∧ False)) ∨ (True → ((False ∨ (p4 ∨ True)) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_578252839696273150078066392940 : (((p3 → (((p3 → p5) → True) → ((p4 ∨ ((p2 → p3) → p5)) → (((p5 ∧ (p3 ∨ p5)) ∧ True) → ((p2 ∨ (p5 ∧ True)) → p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h4.left
    let h21 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h27
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345437593406237650080192958437 : (p3 → (((True ∧ ((((p2 → (p4 ∨ (False ∨ (((False ∨ p5) ∨ (False ∨ (p5 ∧ True))) ∨ p5)))) → p2) ∧ p4) ∨ True)) ∧ (True → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595721563992365405257563778409 : ((((((((p3 → (p4 → p3)) ∧ False) ∨ (False ∨ p2)) ∨ p1) ∧ (((p4 → (p1 → True)) → p5) ∨ ((p1 ∧ p5) ∨ (p2 ∧ True)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44700172975626513967824232211 : ((((((False ∨ p5) ∨ p4) → True) ∧ (((True → p4) → (p4 → ((p1 ∧ p3) → True))) → ((p2 → ((p5 → p3) ∨ p5)) ∧ False))) → p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → p4) → (p4 → ((p1 ∧ p3) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52931418063054120349321006977 : (((((p5 ∨ (p4 ∧ p3)) → (p3 ∧ ((p1 ∧ p1) ∨ False))) ∧ False) ∧ ((False ∨ ((p4 ∧ (p4 → ((True → p3) ∧ p1))) ∧ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318578197233339265527850410738 : (p4 ∨ ((((((((p3 ∧ p5) ∨ p4) ∨ (((p4 ∧ True) ∨ p4) ∨ True)) → False) ∨ (p2 → (True ∧ p1))) ∨ p1) ∨ (p1 ∨ p4)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164750371903682829207347284863 : ((((((p5 ∨ p3) ∨ (p5 ∨ (p2 ∧ (p3 ∨ p2)))) ∨ (p5 → p4)) → (p1 ∧ p1)) ∨ False) ∨ ((True ∨ (p1 → True)) ∨ (p2 ∨ (False ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619542758701306069839864052727 : (((((True ∧ True) ∧ (p4 → ((((p3 ∨ (True ∧ p3)) ∨ p3) ∧ ((((p5 ∧ (False ∨ p2)) ∨ (True ∧ False)) ∧ p4) ∨ p3)) ∨ p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_347017433894898234797271813661 : (p3 → (((False → (p3 → (p3 ∨ p3))) → (p2 → (False ∧ ((p5 ∧ (False ∨ True)) ∨ p5)))) ∨ (((((False ∨ False) → p1) → False) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741403695625592910643787903709 : ((((p5 ∨ False) ∨ (p4 ∧ (p4 ∧ ((p1 ∨ False) ∨ ((((True ∨ (p4 → p1)) ∨ True) → (((p4 → p3) ∧ p5) ∧ (p3 ∨ p5))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158263463191766099999488544345 : (((p2 ∧ (p3 ∨ p1)) ∨ (p3 ∧ ((((p3 → p2) → p2) → ((p5 ∨ p2) ∨ (p5 → False))) ∨ p3))) ∨ ((False ∨ (False ∨ False)) → (p5 ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



