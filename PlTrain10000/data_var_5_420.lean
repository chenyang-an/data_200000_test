variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347324515162813311083890126952 : (p3 → ((p3 ∧ (p5 ∧ ((p1 → ((False → p3) ∧ p4)) → True))) → (((p4 ∧ ((p2 ∧ p4) ∨ p4)) ∧ ((p3 → False) → (p2 ∨ True))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177854866789199937024479510497 : ((((((((p5 → False) ∨ (p5 → p1)) ∨ True) ∧ p2) → p1) ∨ p5) ∨ p3) ∨ (p4 ∨ (((p1 ∧ (True ∧ (True ∨ p4))) ∨ p4) → (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147924809938249241068865142893 : ((((((p1 ∧ (p4 → p5)) ∨ p2) → (p2 → (False ∧ p1))) → ((p2 ∨ (p4 ∨ p4)) → p3)) ∧ (p4 → True)) ∨ (p2 → ((p5 ∨ True) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122915637217150889486228787967 : (((True → (((p2 ∧ (((((p5 → False) ∨ (p2 ∨ p1)) → (False ∨ p5)) → p2) ∨ False)) ∨ p2) ∧ p5)) ∧ ((True → p3) → p3)) → (p2 ∨ p4)) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41297847618444975695099284672 : ((((p5 ∧ (True ∧ (((((p2 → p1) ∨ p1) ∨ p1) → (p4 ∨ p4)) → (p2 ∨ (True → p2))))) → (p1 → ((p1 ∨ True) → p1))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720059830553304360418009237240 : ((((((False ∧ p1) → p4) ∧ True) → ((p1 → (((p4 ∧ (((p3 ∧ p2) → False) ∧ True)) ∨ ((True ∧ True) ∧ p3)) → (p1 ∧ p4))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198179175758721088139168956741 : (((p5 ∨ True) → (((p3 ∧ p2) → p4) ∧ p2)) ∨ ((((p5 ∨ p1) → (((p3 → p2) ∧ p3) ∨ (((p5 ∨ p3) → True) ∧ True))) ∧ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228153590652629057500632561480 : ((p4 ∧ (p5 → True)) ∨ ((((p1 → (p2 → p3)) ∧ ((((p2 ∧ p1) ∨ True) → False) → ((p5 ∨ False) ∧ (True ∧ p1)))) ∨ True) ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165888618756930901577598942367 : ((((p5 ∧ p4) → p4) → (((((p1 ∨ p5) ∧ p3) ∨ p5) → p4) → (p3 → (p1 ∧ p5)))) ∨ ((p1 ∧ (p4 ∧ ((p5 ∨ p4) → p3))) → p4)) := by
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
theorem thm_5_vars_114901287900251386053910370017 : (((p3 → ((p1 → (p4 → p2)) ∧ (False ∨ ((p4 ∧ False) ∧ (p3 ∨ p2))))) ∨ ((True → p5) → ((False ∨ p4) ∨ (p5 ∧ p5)))) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157691059348523725061098152561 : (((p3 → ((((p2 ∨ p3) ∨ p1) ∧ (p1 ∨ p5)) ∨ ((p1 ∧ p2) ∧ p1))) ∨ ((p2 ∧ False) → True)) ∨ (False ∨ ((p1 ∧ True) ∧ (p5 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115799474717978186481497858875 : ((((False → (p2 ∨ False)) ∨ p1) ∧ ((True → ((p4 → (p2 → ((p3 ∨ p2) → (True ∧ ((True ∧ p2) ∧ p1))))) ∨ p3)) → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42884933319516589141175621895 : (((p3 → ((((False → (p2 → (False ∨ True))) ∧ (p4 ∨ p4)) → (p1 → (p5 ∧ (p4 → ((p4 ∨ p5) ∧ (p3 → p2)))))) ∨ p3)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56879336118663150328558758023 : (((p2 ∧ (p5 ∧ p1)) ∧ (((p2 → (p5 → ((True ∨ False) ∧ p4))) ∧ ((((((True ∧ p3) ∧ p3) → p5) ∨ p5) ∨ p5) → False)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757799627472763143450442350643 : (((p1 ∧ (p1 ∨ (((p4 ∨ p5) ∨ (p3 → (p3 → p3))) ∧ (((p4 ∧ p1) ∨ ((p3 → p3) → False)) → ((False ∨ (True ∧ False)) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197113538590285376753481125098 : (((False ∨ (p5 ∧ ((p5 ∨ p5) ∧ p5))) ∨ True) ∨ (((False ∧ p3) → ((p4 ∧ (p3 ∧ (p5 → p1))) ∧ ((p4 ∧ (True ∧ p1)) ∧ p4))) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588292066020608948387138712305 : (((((((p4 ∨ p4) ∨ ((False ∧ True) ∨ p4)) → (((True ∧ (p4 ∧ (p3 → (((p4 → p2) ∧ p3) ∨ False)))) ∨ p2) → p1)) ∨ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200512669445420003710205951308 : (((False ∨ False) → (p1 ∧ ((False ∧ p4) → p3))) → (((True ∧ p2) ∧ ((p5 ∧ (p2 ∨ (p5 ∨ p1))) ∨ ((False → p3) ∨ (True ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109213804037939600408145376101 : ((False ∨ (((((p2 → (p2 ∧ (p3 ∨ False))) ∧ p1) → (p3 ∧ p5)) → (p5 ∧ p5)) ∨ ((True ∧ ((p5 → p5) ∨ p4)) ∨ True))) ∧ (p2 → True)) := by
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
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114681132572015659167644742810 : (((False ∨ ((p3 ∧ p2) ∨ (p4 ∨ (((p2 ∨ (p3 ∨ p2)) ∨ (p2 → p3)) ∧ p4)))) ∨ (((p4 ∧ p4) ∧ (p3 ∧ False)) → p3)) ∨ (p4 ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253722883090599337658320442661 : ((p1 ∧ p1) → ((((((p5 ∨ p2) ∨ (p4 → False)) ∨ ((p5 → False) ∨ ((p2 ∨ False) ∧ ((p1 ∧ False) → p5)))) ∨ (p2 ∨ p1)) → p2) ∨ p1)) := by
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
theorem thm_5_vars_171376153006507316877640419359 : (((((True ∧ (p4 ∧ (p2 ∨ True))) ∧ (p1 → False)) ∧ (p4 ∧ (p1 ∨ p2))) ∧ p5) ∨ ((True → False) ∨ ((p1 → ((p2 ∧ p3) → p1)) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310078489516652348911007708772 : (p2 ∨ ((p3 → (((False → p4) ∨ (((p5 ∧ (p3 ∨ False)) → (p5 → p2)) → p1)) → p1)) → (((p2 ∧ p1) ∨ ((False ∨ p3) ∨ True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_40334716599390692784270787675 : ((((((((True → (p5 ∨ p4)) ∧ (True ∨ p3)) → ((p2 ∧ True) ∨ p5)) ∨ ((((False ∧ p1) → p4) ∨ p1) ∧ False)) ∨ p5) ∨ p3) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694228481093455549784889675595 : ((((((p1 ∨ p3) ∧ (False ∧ True)) ∨ (((False → p3) ∧ True) → (p3 ∨ p3))) ∨ ((((False → False) → p1) ∨ p2) ∧ ((False → p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179188379361686463851304340979 : ((p3 ∧ (((True ∨ ((True → p3) ∧ True)) → True) → ((p5 → p3) ∨ p2))) ∨ ((True ∨ p5) → (True ∨ ((((p4 ∧ p3) ∧ p2) ∨ False) ∧ True)))) := by
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
theorem thm_5_vars_135082827122577719764742987203 : ((((((True → ((p2 ∧ p3) ∨ (True → False))) ∧ True) → ((False ∧ p5) → p4)) → ((True ∧ p1) ∨ p3)) ∨ (p2 ∨ False)) ∨ ((True ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217289544355597881365217145292 : (((p4 ∧ (False ∧ p1)) ∨ p5) → (((p4 ∨ ((((p1 ∨ (p2 ∨ p2)) ∧ False) ∧ True) ∧ p4)) ∧ (p2 → True)) ∨ (((False ∧ p3) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178721201482924873160133956629 : (((((p5 → True) ∨ p2) ∨ p2) → (p5 → ((True ∧ (p1 ∨ False)) ∧ False))) ∨ (True ∨ (((p3 ∨ p5) ∧ (p5 ∧ True)) → ((p4 → p1) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147233370764702040567555346481 : (((((False ∨ (((((((True ∨ p3) ∧ False) ∨ True) ∧ p3) ∧ p4) ∧ (p5 ∨ True)) ∧ p3)) ∨ p5) ∧ p5) ∨ p2) ∨ (True ∧ (True ∨ (p2 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344299033229953173199506482800 : (p2 → (p3 ∨ ((p5 ∨ (((((p2 ∧ p1) ∧ ((p4 ∧ p5) ∧ ((p1 ∨ (p4 ∧ p5)) ∨ p5))) ∨ (p5 ∨ p3)) ∨ True) ∨ p4)) ∨ (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_67473014578128623602485859163 : ((p1 → (((((p4 ∧ False) ∧ p3) ∧ ((((p4 ∧ p2) → False) → p3) → (p4 ∧ p5))) → p2) → ((p1 ∧ (True ∧ p5)) ∨ (p5 ∨ p1)))) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180707133861448039673365923789 : (((((True → p2) → p1) → p4) ∧ ((True → False) ∧ (p3 ∨ (p4 → p1)))) → ((True ∨ ((p2 ∨ False) ∨ (((p5 → False) ∧ True) ∧ p2))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h23 := h19 h22
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h25 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h26 := h19 h25
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h1.left
      let h34 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h38 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h39 := h35 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h42 := h35 h41
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116700519944576940784448587127 : (((False ∧ p4) ∨ (p2 ∧ ((p1 ∧ p1) ∧ ((True ∧ p5) ∨ (True → ((p2 → p5) ∨ (((p3 → True) ∧ (False → p3)) ∧ p4))))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705041660772490076248450216056 : ((((p2 → (False → (True → (((True → False) ∧ p4) ∧ p3)))) → ((p2 ∧ ((p1 → p5) ∨ (False ∧ (p1 ∧ p3)))) ∨ (p4 → (p5 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84041301876027298238079359221 : ((((False ∨ (((p3 ∨ ((True ∨ (p5 ∧ True)) ∨ p4)) ∨ p3) → False)) ∧ (True → p2)) ∧ (True ∨ ((p4 → p5) → (p3 ∧ (p1 ∨ False))))) → p1) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 ∨ ((True ∨ (p5 ∧ True)) ∨ p4)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : ((p3 ∨ ((True ∨ (p5 ∧ True)) ∨ p4)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657712535454150277509794042237 : (((((p3 → p5) → ((False ∨ (p4 → (p2 ∧ (True ∨ (((p1 → ((False ∧ p5) ∨ p2)) → (p4 → p2)) → False))))) ∧ p1)) ∨ (False → p4)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_612619801383176689622434955369 : ((((((p3 ∧ ((p4 → ((((p3 ∨ p5) ∨ True) → (p2 ∨ p4)) → (p5 ∧ False))) ∧ (p5 ∧ p1))) ∨ (p2 → True)) ∨ (p4 ∨ p2)) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304735199186226822775533282423 : (p1 ∨ ((((((p5 ∨ p2) ∧ p1) ∨ True) → (p5 ∧ p5)) → (((True → (p1 → (p3 ∨ False))) ∨ True) ∧ (False → (p1 → p2)))) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113825989579663003307945513321 : (((p5 ∧ (p3 ∨ (True ∨ ((p4 ∧ ((p3 ∧ p3) ∧ True)) → (True ∨ (p4 ∧ (p1 ∧ (p2 → (p5 ∧ False))))))))) → (p1 → p4)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765384416315322401927497012327 : (((p4 ∧ ((p1 ∨ (False ∨ (p3 ∨ (True ∨ ((p2 ∧ (p1 ∧ (((True ∨ p4) ∧ p5) → (p4 ∧ p2)))) ∨ p2))))) → ((False ∧ True) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50362617066313068829477548122 : ((((p3 ∧ (p2 → p1)) ∧ ((p1 → (True ∨ (p3 ∨ p2))) ∧ (p5 ∨ (((p5 ∨ p1) ∨ p4) ∨ p4)))) ∨ (p5 → (True ∨ (p2 → True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47501460559482695936853883907 : (((p1 ∨ ((False ∧ p2) ∨ (((((False ∨ (p2 → (p2 ∧ p1))) → p5) ∨ True) ∧ (p3 ∨ ((True ∨ p3) → p3))) → False))) ∨ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678274490198001105498771126102 : (((((p4 ∨ ((p5 → ((p5 → p1) ∨ p2)) ∨ p3)) ∧ (((False ∨ p4) → False) ∧ ((p5 → p1) → p1))) ∨ ((p2 ∨ True) → (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591067877780605340829009210166 : (((((p5 → (p3 ∨ (((p4 → True) ∧ p3) → (p3 ∨ (p4 ∨ (((p2 → (p2 ∨ (p5 ∧ p1))) ∧ p1) → (False ∨ p4))))))) → p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597040039544070272086123345830 : ((((((p1 ∨ (True → p5)) ∨ (False ∨ p5)) → (((((((p2 → False) ∧ p2) ∨ p5) → p5) → p1) → (p2 ∨ False)) ∨ (p4 ∧ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134746967387296224431263770229 : ((((p5 ∧ p4) ∨ (True ∨ (p4 → (p2 → (False → (((p3 ∨ p2) ∧ (True ∨ p5)) ∨ ((p4 ∨ p1) ∧ p4))))))) → p2) ∨ ((False ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172698154852120839162400932382 : (((p5 ∧ p2) ∨ (p2 → ((p1 → (((p4 → p2) ∧ (p5 ∨ p5)) → p3)) ∧ p1))) ∨ (((p1 → (True ∧ ((p4 ∧ True) → p4))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172319840226114506596429364237 : (((p5 → (((p2 ∨ True) ∨ (p1 ∨ p2)) ∨ True)) → (False ∨ ((p5 → False) ∧ p4))) ∨ (p5 → ((p5 ∧ (p3 ∧ True)) ∨ ((True ∧ p1) → p1)))) := by
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
theorem thm_5_vars_318853320316815566277377999118 : (p4 ∨ ((((True ∧ (((p5 ∧ (p4 ∨ p3)) ∨ p3) ∨ p1)) → (p3 → (False ∧ (p4 ∨ (p3 ∨ (p1 ∧ p2)))))) ∨ p2) ∨ (True ∨ (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52764363997890255810081342178 : (((((True → p3) ∧ (((False → False) → False) ∨ ((p1 ∨ True) → p4))) → p1) → (((p2 → (p4 ∧ False)) ∧ (False ∨ p2)) ∨ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328997639665629896036189063079 : (True → (((p3 ∨ True) → ((p4 ∨ p2) ∧ p1)) ∨ (p3 → ((((p2 ∨ p2) ∧ p2) ∨ (True → ((p5 → (p4 ∧ (p4 → p2))) ∧ p5))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781561145178943729386005706718 : (((p2 ∨ (False ∨ (((p4 ∨ (p3 ∨ (p1 ∧ p1))) ∧ ((((p5 → p5) ∨ p2) → (p3 → False)) → p5)) ∧ (True ∨ (p3 ∨ (p3 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21916774623592876694742531071 : ((((p2 ∧ (p3 → p4)) ∨ (p5 → (p4 ∨ True))) ∧ (((((p1 → False) → p2) ∧ p5) ∨ p1) ∨ ((p3 → (p2 → (p5 → p3))) ∨ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344287388169728528301246559796 : (p2 → (p3 ∨ ((((p1 ∧ ((p4 ∧ (p5 ∧ p3)) → p5)) ∨ (p1 ∧ ((p4 ∧ p5) → p4))) → ((p2 ∨ True) → ((p2 → p5) ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199521231436878834394203211526 : (((p5 → (False ∧ ((p3 ∧ p5) ∧ p3))) ∨ p3) → ((p4 → p2) → (((p1 ∨ (p2 ∨ (p5 ∨ True))) ∨ ((True ∧ False) → (p2 → True))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956187565599449346433566834895 : (((((False → p1) ∨ False) → (((p3 ∧ (((p2 ∨ (p5 ∧ (p1 ∨ (p3 ∨ p1)))) ∧ (p5 ∧ p1)) ∧ (p3 ∨ False))) → (p4 ∧ p5)) ∧ p4)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p1) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594421606670648400329542028711 : (((((True → (((True ∧ p5) ∧ ((p1 ∧ True) ∧ p2)) ∧ (p3 ∨ (p5 ∧ (p1 → False))))) ∧ ((p4 ∨ (p5 → True)) ∧ (p3 ∨ False))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190811209038403145690017881844 : ((((p3 → True) → (p2 ∧ (p4 ∧ p2))) ∨ (p2 ∨ False)) ∨ (((((p2 ∨ (((p3 → True) ∨ p5) ∨ p2)) → p1) ∧ False) ∧ p4) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_149552961079676101216026693043 : ((p2 ∧ (((p4 ∨ ((False ∧ (p1 ∧ True)) → p4)) ∧ (p2 → p3)) ∧ ((p3 ∧ p3) ∧ ((p4 ∧ p2) ∨ p1)))) ∨ ((False ∨ False) → (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119139094413617428417731699698 : ((p1 → (p5 ∨ ((True ∧ (p5 ∨ (p3 → p3))) → ((True ∨ (p3 ∨ p3)) → ((True → ((p4 ∧ p3) → p4)) ∧ (False ∨ True)))))) ∨ (p1 ∨ False)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h2.left
      let h16 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h2.left
      let h21 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h2.left
    let h26 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
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
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h2.left
      let h32 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h2.left
      let h37 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
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
theorem thm_5_vars_725926785571149502011948205867 : (((((p2 → False) ∧ p2) ∨ (((((((((False → False) ∧ True) → False) ∨ (p5 → p5)) ∧ ((p3 ∧ p5) → True)) → p2) ∧ False) ∨ False) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_134080266889752422377056944450 : (((((False → ((p5 ∧ (False ∧ ((p3 ∧ p3) ∧ False))) ∨ False)) ∧ ((p1 ∨ p2) ∨ (p5 → (p1 ∧ p3)))) → p2) ∨ True) ∨ (p3 ∧ (p5 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41342236243243298459680608287 : ((((((p3 → p1) → (p5 ∨ (p3 ∨ p2))) → (True ∧ ((p3 ∨ (p3 ∧ p4)) → p2))) ∨ (((p1 → p2) ∨ (False ∨ True)) ∨ p5)) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59324560843509603192069457232 : (((p4 ∨ p3) ∨ (((((False ∨ p4) ∨ (p1 ∨ False)) → p5) → p4) ∨ (p3 ∨ ((False ∨ p2) ∧ ((p2 ∧ ((True ∧ p2) ∨ False)) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338985991741448193128562190651 : (p1 → ((p5 → p3) → ((((((((p5 ∧ p3) → p4) → p3) ∨ True) → (p3 ∨ False)) ∨ False) ∨ ((p1 ∨ False) → p1)) ∧ (p1 ∨ (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27748038684562963671311739542 : (((p3 ∨ p3) → ((p3 → (((p5 ∧ (p1 → p1)) ∨ ((((p2 → p5) → p1) ∨ p5) → (p1 ∨ True))) ∨ (p3 ∧ (p3 ∧ p4)))) ∧ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342385549376264697748883506840 : (p2 → (((p2 → (p2 ∨ ((((True ∨ p3) → p2) → (p1 ∧ p5)) → (p5 ∧ p5)))) → p3) ∨ ((p1 → p4) → (p5 ∨ ((p1 → p2) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48467344872821170754910915743 : (((((((p1 ∧ True) ∨ p4) ∨ ((True ∧ p3) → (p1 → (p1 ∨ ((p3 ∧ True) ∨ p3))))) ∨ (p3 ∨ p3)) ∧ p4) ∧ (False ∧ (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162338442959264316713907770620 : ((((((True → (((True ∧ (p1 ∧ p5)) ∨ p2) ∧ True)) → (p5 ∧ p1)) ∨ True) ∨ True) ∨ p1) ∧ ((False → (((p5 → p3) ∧ p5) → False)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324221760543124657361477821896 : (p5 ∨ (((((p4 ∧ p1) ∨ p1) ∨ (True ∧ p4)) ∨ True) ∧ ((True → (False ∧ (((False ∨ True) → (p2 ∧ (False ∨ p4))) ∨ p2))) → (p1 ∨ p4)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606962569483499875627202522210 : (((((((((p2 ∨ (p2 → p5)) → True) → ((p3 → p3) → (p3 → True))) → p3) ∧ (p3 ∧ (p2 → ((p4 ∧ p5) ∧ False)))) ∧ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_56629118925732009283040408981 : ((((p3 ∧ p4) ∧ p2) ∧ (p5 ∨ (((True → (((((((p5 ∧ p2) ∨ p2) ∧ p3) → p5) ∨ (p3 ∧ p5)) → p4) → False)) ∨ p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59226557894835051775211932880 : (((p2 ∨ False) ∨ ((p5 → (p4 → ((((p1 ∨ True) ∧ p4) → ((p3 ∨ p1) ∧ (p1 ∧ (p4 ∨ (p5 ∨ (False → p1)))))) ∧ p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722007087795592858087418980754 : ((((False → (p1 ∧ (p1 → p1))) → ((p2 ∨ ((p4 → True) → (p1 ∧ (p2 → (False ∨ ((p3 ∨ p1) ∧ (True ∧ (p5 ∧ p2)))))))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_217284746357159896814205514343 : (((p3 ∧ (p5 ∨ False)) ∨ p5) → ((p2 ∨ (p4 → (((p2 ∧ p3) ∨ False) ∧ (p5 ∧ (p5 → p4))))) ∨ ((p1 → False) ∨ ((p2 ∨ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8906741067526853839433345620 : ((((p1 ∨ (True → ((p3 ∨ (((p4 → p3) ∧ p3) ∧ (p5 ∨ ((p5 ∧ p4) → p3)))) → p4))) ∨ (p1 → (p3 ∧ (p5 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183802162944246810704915781900 : (((((p2 ∨ (p3 ∨ p2)) → (p5 ∨ (True → False))) ∨ p3) ∧ False) ∨ (p2 → ((p5 ∧ (p4 ∨ ((False ∨ (p3 → (p3 → p4))) ∧ p2))) → p5))) := by
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218331086284245040326808934820 : (((False → p2) ∨ (p5 → p4)) → ((p4 ∧ ((p5 ∧ ((p3 → p1) ∨ p1)) ∧ True)) → ((((p1 → p5) ∧ (p2 ∨ p3)) ∧ (p3 → p2)) → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h2.left
    let h23 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197931317561099624721811108384 : (((p4 → (p4 ∧ p2)) → ((p5 ∧ p1) ∧ False)) ∨ ((p5 ∧ False) → (((False ∧ (((p1 ∧ ((p4 → p3) → p2)) ∧ p1) ∨ p4)) → p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_111171089638584270623057180993 : (((((p2 ∨ (p1 → p5)) ∧ False) ∨ (((p5 → ((p3 ∧ p3) → (p3 ∧ ((p3 ∨ p2) → (p3 ∧ p1))))) ∧ p4) → p5)) ∧ p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66798353681644810579928357858 : ((True → (p2 ∨ ((p5 → (p5 ∧ p5)) → ((p3 ∧ ((p3 ∨ p2) → (p1 ∧ ((p3 → (False ∧ p3)) ∧ ((p3 ∧ p4) ∨ p2))))) ∨ True)))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797344025971298260157611728918 : (((p1 → (((((p2 ∨ ((False ∧ (p3 ∨ p5)) ∨ p3)) → p4) ∧ (False ∨ p3)) → (((p5 ∧ p3) ∧ p1) ∧ ((p2 ∧ p3) ∧ p3))) ∨ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42580303794608879169212561470 : (((p2 ∨ ((p5 ∨ ((((((p4 ∨ True) → ((False → True) → p2)) ∧ False) ∧ True) ∨ p4) ∨ (p4 ∧ p5))) → ((True → False) ∧ p2))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53895002860991063896482271858 : (((p1 ∧ (((p2 ∧ False) ∨ p1) → ((p3 ∧ p4) ∨ False))) ∨ (((p2 ∨ (p3 ∨ (p2 → (p4 → (p2 → p5))))) ∧ (p3 ∨ True)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655194502611365197615180284812 : ((((((p2 ∨ (((p4 ∧ (p2 ∨ p3)) ∧ ((p5 → ((p2 ∧ p3) ∨ p3)) → p5)) ∨ (True → p2))) ∧ p1) ∧ (p3 ∨ p1)) ∨ (False → p3)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_193782746145824444315517510530 : ((p4 ∧ ((p4 ∨ ((p4 ∨ False) ∧ True)) ∧ (p5 ∧ p3))) → (((((p5 → p3) ∧ p4) ∧ (p1 ∨ (p2 ∨ False))) ∨ (p2 ∨ (p4 ∨ p4))) ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h19.left
      let h28 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305173759464796870231626809065 : (p1 ∨ (((p2 → ((((p5 ∨ True) ∧ p3) ∨ (p5 ∧ (p4 ∧ p4))) ∧ p5)) ∧ (((False ∨ p4) ∧ p5) ∧ p5)) ∨ ((p4 → True) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_115336837214664816919643577963 : (((False ∨ (True ∨ ((False ∧ ((True ∨ p4) ∨ False)) ∨ p5))) → (((p2 → ((False → (p5 ∨ p5)) → p5)) ∨ p2) ∧ (p2 ∧ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134984499404432512088431987712 : ((((p3 → p4) ∧ ((p1 → ((p3 ∨ True) ∧ p4)) ∧ (True ∧ (((p1 → (p3 ∨ p3)) ∧ p4) ∧ False)))) ∧ (p4 ∨ p3)) ∨ (p4 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117079578136677754134890406007 : (((False → False) → (((p1 → (p5 ∧ (True ∨ (p1 ∧ p2)))) ∧ p2) → (p3 ∧ (p3 ∧ ((p1 ∧ (p5 ∨ (p4 ∨ p3))) ∨ False))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345544122261403790488685140009 : (p3 → ((((True → (p5 ∨ p1)) ∧ (p5 → p4)) ∧ (((p1 → (((p4 ∨ p1) → p3) ∨ p5)) ∧ False) ∨ ((False ∧ p2) ∨ (p2 ∧ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941747227050530586414619895333 : ((((False → (p1 → (p1 → (p5 ∨ p2)))) → ((((p3 ∧ True) ∨ (p3 ∨ p1)) ∧ ((p2 → ((p4 ∨ p3) ∧ p4)) ∧ p2)) ∧ (False → False))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 → (p1 → (p5 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159090991958066997450324420900 : ((True → ((p4 → ((p5 ∨ (p3 ∧ (p3 ∧ (p5 → (p2 ∨ True))))) ∧ (False → p1))) → (p2 → p3))) ∨ ((p5 ∨ ((p1 → p3) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662707269040235899447231164985 : (((((True ∧ (p2 ∨ (p3 → p4))) ∨ (((p5 ∧ (True ∨ (((False → (p5 ∧ p4)) ∧ (p2 → False)) ∧ p5))) → p3) ∧ p1)) → (p3 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117564525922000631947899486972 : ((p2 ∧ (((p4 ∨ (p4 ∨ False)) → True) ∧ (((p3 → ((((p2 ∧ p4) ∧ p3) ∨ p4) → p1)) ∧ p1) → (False ∧ (p3 → p1))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356893801706037905741619427156 : (p5 → ((((False ∨ False) ∧ p2) → p4) → ((p5 ∨ ((p3 ∧ p3) ∨ (p1 ∧ (False ∧ p3)))) → (p1 ∨ (p1 ∨ ((p4 ∨ p4) ∨ (p3 → True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345834290078744920318151109834 : (p3 → ((((True → (p1 ∧ (False ∧ (((p5 ∧ (p1 ∧ p3)) ∧ p2) ∨ p4)))) ∨ (((True ∨ (p3 → p5)) → (p5 → True)) ∨ p2)) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True → (p1 ∧ (False ∧ (((p5 ∧ (p1 ∧ p3)) ∧ p2) ∨ p4)))) ∨ (((True ∨ (p3 → p5)) → (p5 → True)) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351449060813478951601493425455 : (p4 → (((((p2 → ((p1 ∧ True) → (((p3 → p2) ∧ p5) ∨ p3))) ∧ False) → p1) ∨ (True ∨ (p4 ∧ p2))) → (p5 ∨ ((p4 ∧ p2) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792445581580985630805666860995 : (((True → ((p2 ∧ (True → ((False ∨ False) ∨ (((p4 ∧ p4) → False) ∧ p4)))) ∨ (((True → p5) ∨ p2) ∨ ((False ∨ p4) ∨ (False → p4))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



