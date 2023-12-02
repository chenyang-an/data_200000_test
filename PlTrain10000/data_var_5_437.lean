variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64068212601466792640177617431 : ((False ∨ ((((p5 → (p2 → p3)) → ((p2 ∧ p4) → ((p4 ∧ (p2 ∧ False)) ∧ p4))) ∨ p2) ∨ (p4 ∧ ((p2 ∧ (p3 → p1)) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57605233554079397048054063737 : ((((p3 → p2) ∧ p2) → ((((True ∧ (p1 → (p1 ∨ p1))) ∧ ((True ∧ (p3 ∨ (p2 ∧ p4))) ∨ ((p2 ∧ p1) ∨ p4))) ∨ p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_689634688886354540478743841247 : (((((p4 → ((p1 ∨ p1) ∨ (False ∨ p5))) → (p1 ∨ (((p1 → p5) ∨ p2) ∨ p5))) ∨ ((p2 ∧ False) → ((False → (p4 → p2)) ∧ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349667813247581945591110703914 : (p4 → ((((((False → p3) → (p4 ∧ (p5 ∧ p4))) → ((p4 → ((p2 → False) → (False ∧ p4))) ∧ p3)) ∨ p4) ∨ (p1 ∨ (p3 ∧ p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307850220273664696602081868088 : (p1 ∨ (p5 → (((p5 → ((p1 → p5) ∧ p2)) ∧ (((p5 ∧ (p5 ∨ ((True → ((p4 ∧ p4) → True)) ∨ p4))) → (p1 → p4)) ∨ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42024984772211158405221421722 : ((((p1 ∧ p1) ∨ (((p4 ∨ (p3 ∧ ((p2 ∨ ((p3 → p1) ∨ (((True ∧ True) ∨ (p2 → p2)) ∨ True))) → p5))) ∧ p4) ∨ p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809261867697440765098808559165 : (((p5 → (((((p1 ∧ True) → (p2 → False)) ∧ p2) ∧ (((p4 ∨ (p2 → (p5 ∧ ((True ∧ (p1 → p1)) ∧ p5)))) ∧ p4) ∧ p2)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619301077596877051453714388493 : ((((((p5 ∧ p4) ∨ True) → ((p1 ∨ (p4 ∨ (((False → (p3 ∧ False)) ∨ ((p3 ∧ p1) ∧ p1)) ∧ (False ∨ (p5 ∧ p4))))) ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_726857934700796403875163357879 : (((((p3 ∨ p1) → p5) ∨ (((p2 ∧ ((True → (p3 ∨ (p3 ∧ p5))) ∨ ((((p5 → p3) ∨ p1) ∨ True) ∨ True))) ∨ p3) ∨ (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306138277847892449267260090509 : (p1 ∨ ((p4 → (False → p2)) ∧ ((((p4 ∨ p3) ∧ (p1 ∨ ((p2 → p1) → p4))) ∨ (False → (p5 ∨ p5))) ∨ ((p5 ∧ (p5 ∧ p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304755348262292289032772902505 : (p1 ∨ (((p5 ∧ p3) → ((p5 → (((((((p3 → p1) ∨ p2) → True) ∨ p4) ∧ p4) → ((True ∧ True) ∨ p2)) → p1)) ∨ p5)) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_752163678304606376825628124562 : (((True ∧ (p2 → ((((p1 → p1) ∧ p4) → (p3 ∧ True)) → (p4 ∧ ((p4 ∨ ((p2 ∨ (True ∨ p2)) ∧ (False ∨ (p2 ∧ False)))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811635486077939825024372866146 : (((p5 → (p1 → ((((p1 ∧ False) ∧ ((p1 ∨ (True → (p5 ∧ p2))) ∨ p3)) → (p2 ∧ p3)) → (p3 ∧ (p2 ∨ ((p4 ∧ p5) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749411682590755167043874132914 : (((True ∧ (((((p1 ∧ False) ∨ ((False → p5) ∧ p3)) ∨ (((p3 ∨ (p5 ∧ p2)) → True) → ((p4 → p2) ∧ p3))) ∨ (p3 → True)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213652429781330635767236028814 : ((((p4 ∨ False) ∨ False) ∨ p4) ∨ (p1 ∨ ((((((p5 → True) ∨ p4) → p5) ∨ ((p1 → (False → p4)) ∨ ((p5 ∧ p2) ∨ False))) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42638749147547519607409608042 : (((p3 ∨ (p4 ∨ (((p5 ∨ (p2 ∨ p3)) ∧ p4) ∨ ((p3 → (((p3 ∧ (p5 ∨ p3)) → (p2 ∨ (p2 ∧ p4))) ∧ p4)) ∨ False)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155819074875630810076997841838 : ((True ∧ ((((p5 → True) → p2) → (((False ∨ p4) ∨ ((p4 → p5) ∨ p5)) ∧ p5)) ∨ (False → p1))) ∧ (False ∨ (((p3 ∧ False) ∨ True) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257852094349921336085230621002 : ((p4 ∨ True) → (((((((p4 ∧ p2) → p2) ∨ True) → False) → (False ∨ ((p2 ∧ ((p1 → (p3 ∧ p2)) ∨ True)) ∨ (p4 → p1)))) ∨ False) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 ∧ p2) → p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((p4 ∧ p2) → p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52140624585629380622907859539 : ((((p2 ∧ ((p5 ∨ p2) ∨ (False → (p4 ∨ (False → (p2 → True)))))) ∨ (True ∨ p1)) → (p4 → ((p5 ∨ p3) ∨ ((False → p3) ∨ False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147725162598264112015886153845 : (((((False ∨ p4) ∧ ((p4 ∨ p1) → p4)) ∧ ((True → ((((True ∧ p5) ∨ True) ∨ p4) → p5)) ∨ True)) → False) ∨ (False → (p5 → (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86531671172384899091771361091 : (((((((p1 ∨ p5) ∨ p1) ∨ p5) → p2) ∧ p3) ∧ ((True ∧ ((((p5 → (p1 ∧ False)) ∨ (True → p2)) ∨ p3) → (p5 ∨ p1))) ∧ True)) → p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (((p5 → (p1 ∧ False)) ∨ (True → p2)) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (((p1 ∨ p5) ∨ p1) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : (((p1 ∨ p5) ∨ p1) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179349388885262019925096981832 : ((p1 ∨ (p3 → (((p2 ∨ False) ∨ (((p4 → p5) ∧ p2) → p3)) → p4))) ∨ ((p2 ∨ True) → (p2 ∨ (((False → p2) → (p3 ∧ p5)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40372306253596610097417032986 : (((((False → ((p1 ∧ ((((False ∧ (False ∧ (((p4 ∨ True) ∧ (p2 ∧ p1)) ∧ False))) ∧ p3) ∨ True) → True)) ∧ p2)) → p4) ∨ True) ∨ p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40038228605693108882785358504 : ((((((p4 ∧ p2) ∧ ((((p3 ∧ p2) ∨ (p4 ∨ False)) ∧ ((False ∨ (((False → p1) ∨ p3) ∧ False)) → p4)) → False)) ∧ p1) ∧ p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58100691402521067821698611322 : (((p1 ∧ p2) ∧ (p3 ∨ (((p5 ∨ ((p1 → p5) → (((p4 ∨ p4) ∨ p5) → (p3 ∧ False)))) ∧ p3) ∨ (((p3 ∨ True) ∨ p3) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174501315937983593170307432540 : ((((p1 → (p3 → (p5 ∧ p2))) → p2) ∨ (p4 → (p1 ∧ ((False ∨ True) ∨ True)))) → ((p3 → (p3 ∧ False)) ∨ ((False → p3) ∨ (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111276098572319320325043397829 : ((((p5 ∧ p3) → (((p2 → (p2 ∨ True)) ∧ p1) ∧ (p1 ∧ ((((p2 ∧ p3) ∨ ((False ∨ p1) ∨ p4)) → p4) ∧ False)))) ∧ False) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134952754507312372802978262389 : ((((p4 ∧ (p1 → (p3 ∨ ((True ∨ (p2 → (p3 ∨ (p4 → p2)))) ∨ True)))) → (p4 ∧ (True ∧ False))) ∧ (p2 ∨ p5)) ∨ (p3 → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329708945184060857526065484059 : (True → ((False → True) → (False ∨ ((p4 ∧ ((p2 → (p1 ∨ True)) ∧ True)) → (p4 → (p4 → (((p3 ∨ (p2 ∧ (p4 → p3))) ∨ True) ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300456195658322312589674366568 : (False ∨ (((((False ∧ p3) ∧ p2) ∨ True) → (False ∧ (((((p5 ∧ p1) → p2) → (p3 ∨ p2)) → (True ∧ p4)) ∨ True))) → ((p3 ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p3) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135667485852691628129342815102 : (((True ∨ (((p2 → p4) ∨ p1) ∨ (((((False ∨ p2) ∧ True) → p2) ∨ p3) ∨ p5))) → ((p4 → (p3 → p1)) ∧ p5)) ∨ ((True ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257306201552885647076444863431 : ((p2 ∨ p4) → (((False ∨ (((False ∧ p3) ∧ False) → (p2 → ((((p2 ∧ p2) ∧ ((False ∧ False) → (p2 ∨ p4))) ∧ p2) → p1)))) → p5) ∨ True)) := by
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
theorem thm_5_vars_165750560311593135090951283983 : (((False ∧ ((True → p2) → p5)) ∨ ((((p2 ∨ (p3 ∧ True)) ∧ (p3 ∨ True)) ∨ False) → p3)) ∨ (((p5 → p2) → p4) ∨ ((False → p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137130007184969097498620023806 : ((True ∧ (False ∧ (True → ((p4 ∨ (p2 ∧ (((p4 → (p4 ∨ p3)) ∧ ((p5 ∧ p5) ∧ p4)) ∧ (p3 ∧ p1)))) ∨ p1)))) ∨ ((p2 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608164085197730555385266652487 : (((((((p1 ∧ p5) ∨ (p2 ∨ ((p5 → ((True ∨ p3) ∧ p1)) → ((p1 → (p2 ∨ ((p4 ∨ p3) → p4))) ∨ p1)))) ∧ p2) ∨ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_619408156271234797842477236218 : (((((p1 ∧ (p5 → p1)) → (True → ((False ∨ (False ∨ (p4 ∨ p3))) ∧ ((p2 → (p1 → (p2 ∧ ((p4 ∧ True) ∨ False)))) ∧ True)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_122171941226808477805333938534 : ((((((False → p5) → p1) ∧ ((True ∨ (((p4 ∨ ((p5 ∨ p3) ∨ p3)) ∧ p2) → p2)) → True)) ∧ (p5 → p3)) ∧ (p1 → False)) → (True → p2)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h9
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49551205612182643964084697303 : ((((((p1 ∧ True) → p1) ∨ (False → ((p5 → (p4 ∧ p2)) ∧ (p4 ∨ (True ∨ p5))))) ∧ ((False → p1) ∧ p4)) → (False ∨ (p2 ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704503539741879539869326523663 : (((((p5 ∧ p4) ∧ (p3 → (p1 ∧ ((p1 ∨ True) ∨ p1)))) → ((p3 → False) ∨ (p3 ∨ (p5 → ((False ∨ ((p5 ∨ False) → p4)) → p5))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136163088085571625289718815923 : (((p4 ∨ (p3 → ((p5 ∨ (p1 → False)) ∨ p4))) → (((False ∨ (p1 ∧ p4)) → ((p5 → p3) ∧ (p3 ∧ p4))) ∨ p1)) ∨ ((True → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149399757988182177505875914157 : ((True ∧ ((p3 ∨ (((p2 ∨ False) ∧ p5) ∧ ((p5 ∨ ((((p5 ∧ True) ∨ False) ∧ p2) ∨ p4)) → p3))) ∨ p2)) ∨ ((p1 ∨ False) → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231629781671706479495371573005 : (((False ∧ False) → False) → ((p5 ∨ p1) ∨ (p3 ∨ (((False → True) ∨ True) → (p2 ∨ ((p4 ∧ (False ∧ (p5 ∨ ((p4 ∧ p1) → p3)))) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51290569966121441814403420946 : (((p4 ∧ ((p1 ∧ (p1 ∨ False)) → ((p3 ∨ ((p2 → (p4 ∧ (p4 ∨ p1))) ∨ p3)) → p4))) ∨ (((False ∧ True) ∧ (p3 → p2)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215294962255466256267798055824 : ((p1 ∧ ((False ∧ p5) ∨ p3)) ∨ (((p3 ∧ p4) ∧ (p5 ∧ ((((p3 ∨ ((p5 ∨ p5) ∨ p2)) ∧ (p4 ∧ (p3 ∧ False))) ∧ p5) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303965446849114603127423565766 : (p1 ∨ (((p4 → (p3 ∨ p3)) ∧ ((p1 ∧ (p3 → True)) → ((((p1 ∨ p3) ∧ p4) → p1) → (p2 ∨ ((False ∧ False) ∧ (p1 ∧ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_935274611143660498305471308712 : ((((((p1 ∨ p3) ∨ ((p4 ∧ p2) ∧ p2)) → True) → ((p3 ∧ ((p2 → ((p4 ∧ p2) ∧ ((p3 ∨ (p5 ∧ p4)) → p5))) ∨ p2)) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p3) ∨ ((p4 ∧ p2) ∧ p2)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719166645432951108661178790376 : ((((p1 ∧ (p2 → (p4 → p5))) ∨ (p1 ∨ ((p5 ∨ p5) → ((p2 → p3) ∨ (((p5 → p5) ∧ p1) ∨ ((p3 ∨ (p3 ∨ p5)) ∨ p2)))))) ∨ p3) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199811893238324557464541685443 : (((((p2 ∧ p2) ∨ True) → False) ∧ (False ∨ p5)) → ((p3 → (p1 → (False ∧ (((p2 → False) ∧ (((p3 ∧ p4) → p3) ∨ p5)) → False)))) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h18 : ((p2 ∧ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h19 := h14 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h25 : ((p2 ∧ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h25
      -- False on the left can always be used.
      apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h29 =>
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h31 : ((p2 ∧ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h32 := h27 h31
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323422754850908746514140059115 : (p5 ∨ (((False ∨ (((p4 → ((p2 ∧ (False ∧ (p2 ∧ ((False → p4) ∨ False)))) → False)) → p1) ∨ p3)) ∨ (p3 → True)) ∧ (p1 ∨ (p1 → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60084771930601120873409277324 : (((p2 ∨ p5) → ((p2 → p3) → (((p5 → p2) → (False ∨ (p3 → (((p4 → (True ∨ False)) → p3) ∨ (p5 ∧ (False ∨ True)))))) ∨ p5))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60839612602202812096434327479 : ((True ∧ (p1 ∨ ((False ∨ (((p2 ∨ (((((False ∨ False) ∧ False) ∨ (False → False)) ∧ p3) → p2)) ∧ (p1 → p3)) ∨ p3)) → (p4 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214193610014749676952363937512 : ((((p4 ∨ p2) → p1) → p5) ∨ (p4 ∨ (p4 → ((((p5 → True) → (((False → p1) ∨ p2) → (True ∧ (p5 → (p1 ∨ p4))))) ∨ p1) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
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
theorem thm_5_vars_258419141961043264152644561302 : ((p5 ∨ p1) → (((p5 ∨ ((p3 ∨ ((p4 ∨ p3) ∨ True)) → p1)) ∧ ((True ∨ p3) ∧ (False ∧ p3))) ∨ ((((p2 ∨ p1) ∧ True) ∨ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597289148174389752799222141287 : (((((p3 ∧ (p4 ∧ (False → True))) ∧ (((((p4 → p4) ∨ ((p4 ∨ (True → False)) ∧ (p4 → p5))) → p4) ∨ p5) ∨ (False → p3))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57669653368788975524076050321 : ((((False → True) ∨ False) → (((p2 ∨ (p1 ∨ p5)) → ((p1 ∨ False) ∨ (p1 ∧ (False → (True ∧ (p2 ∨ (p5 ∨ p2))))))) ∨ (p4 → p4))) ∨ False) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740833895352399394151592238308 : ((((p3 ∨ False) ∨ ((((False ∨ p1) → (p2 ∧ p3)) ∨ ((p1 ∧ p1) ∨ (((True ∧ p1) ∧ ((p2 → p1) ∧ p1)) → p4))) ∨ (False → p1))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176650340858673393270190748368 : ((((p4 ∧ p5) ∨ (p5 ∧ p3)) ∨ (False ∨ ((p4 → True) ∨ (p3 ∨ p1)))) ∧ (((p5 ∧ p3) → (p5 → True)) ∧ (False ∨ (p2 ∨ (p1 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
theorem thm_5_vars_341844734371870195864580843213 : (p2 → ((((p2 → p2) → (p5 ∧ False)) → ((p5 ∧ p1) ∨ ((((p5 ∨ (False ∧ p5)) ∨ True) → (p3 → True)) ∨ (p2 → p4)))) → (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178331000558250332450932786826 : (((((p1 ∧ p2) ∨ (p1 ∨ p5)) ∨ (p1 ∨ (False → p3))) ∨ (p2 ∨ p5)) ∨ ((p1 ∧ True) ∧ ((p4 ∨ p5) → (True ∨ (p4 ∨ (p3 ∧ p5)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64146128061079269947568169140 : ((False ∨ ((p3 ∧ (p1 ∨ p4)) ∨ (p1 ∨ (False ∨ (p4 ∨ (True → (False ∧ (False ∧ (True → ((True → ((p3 → True) ∧ p4)) ∧ p2)))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142454045695458493795986295856 : ((p5 ∧ (((p1 ∨ p4) → (p2 ∨ (p3 → (p1 ∧ ((p4 → True) ∧ (p2 ∨ ((p1 → (p4 ∧ p4)) ∧ True))))))) → p2)) → ((p3 → False) ∨ p5)) := by
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
theorem thm_5_vars_227161986838771379868008557085 : (((p5 ∨ p3) → p3) ∨ (p5 ∨ (((p3 → p2) → True) → (((((p5 ∧ p4) ∨ p1) → (p3 ∧ (p1 ∧ p2))) ∨ (p2 ∨ (p1 → p1))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261341583714274210862774096067 : ((p5 → False) → (((p4 ∧ True) ∨ (p3 → (p4 ∨ p1))) → (True ∧ ((((False ∨ p4) ∨ p3) ∨ p3) → (p5 → (False ∨ (p1 ∧ (False → p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h12 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h13 := h1 h12
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h15 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h16 := h1 h15
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h22 := h1 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h25 := h1 h24
        -- False on the left can always be used.
        apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h30 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h31 := h1 h30
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h33 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h34 := h1 h33
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135159641975941572757462326470 : (((p5 → ((p1 ∨ False) ∧ (((p1 ∨ ((True ∨ False) ∧ (p2 → (p4 ∨ False)))) ∧ (p1 ∧ False)) ∧ p4))) ∨ (p3 → p3)) ∨ (p1 ∧ (p4 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327837883151398145146532427725 : (True → (((p5 ∨ (((p2 → p5) → (p1 → ((p4 ∨ p5) ∧ (p5 ∨ (p5 ∨ p3))))) → p4)) ∨ ((p3 → True) ∧ (True ∨ p3))) ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670356850595376601822874571478 : ((((((False ∨ p3) → p5) ∨ ((p1 ∨ (((p4 ∨ p1) ∨ (p1 ∨ p3)) ∨ ((p1 → p3) → (p4 → False)))) ∨ True)) ∨ ((True → p1) ∧ p3)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118859866378382016065255045822 : ((True → ((((p2 ∨ True) ∨ (p1 → False)) ∧ False) ∧ ((False ∧ p3) ∨ (p5 ∨ ((True → ((p4 ∧ p1) → (True → p3))) ∨ True))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669547295847229090111514558963 : (((((p2 → ((((p5 ∧ p2) → ((p1 ∧ (p3 → (p5 ∨ p1))) ∧ (True → p5))) ∧ p4) ∨ True)) → (False ∨ p1)) ∨ ((p2 → p4) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255751290273227543271525156421 : ((True ∨ True) → ((p5 ∨ ((p2 ∧ (((True → True) → p1) ∨ p1)) ∧ True)) ∨ ((False ∧ ((False ∧ True) → ((p5 ∨ p2) ∨ (p5 ∧ False)))) → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350136164118807088563016094347 : (p4 → (((((p4 ∨ (p1 → (p5 → ((True → p2) → p3)))) ∧ p1) → (p5 ∨ p3)) → ((((p2 ∨ p3) ∨ True) ∨ p3) ∧ (p5 → True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41015783644960384145701595245 : (((((True ∨ ((p2 ∧ (False ∨ p5)) ∨ (((False ∧ (p5 ∧ p3)) ∨ ((True → (p1 ∨ True)) ∧ False)) → p4))) ∨ False) → (p5 ∧ p1)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648390618459096374777097512855 : ((((((((p4 ∧ p4) ∧ (True → (p1 → ((p5 ∨ p3) ∨ False)))) ∨ ((((p5 ∧ p5) ∧ False) ∧ p5) ∨ False)) ∨ False) ∨ p1) ∧ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114416007552066735561479288951 : ((((p5 ∨ p1) ∧ ((p4 ∧ p3) ∨ ((((False → False) ∨ p4) ∧ (p1 ∨ p5)) ∨ (True → p5)))) ∨ ((p2 ∨ p5) ∨ (True ∧ p5))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232406905642140868011617006630 : (((p5 → p5) → p2) → ((((((False ∧ (((p3 ∨ False) → False) ∨ p2)) ∨ ((p1 ∧ (p1 → (p4 → p2))) ∧ p2)) → False) → p4) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768653371695590466258322604791 : (((p5 ∧ ((((p5 ∨ (True ∧ (p3 → p2))) ∧ p4) ∧ (False ∨ (p5 → p2))) → ((p2 → (p3 ∨ False)) ∧ ((p3 ∧ p3) → (p4 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151929790988218256958941467491 : ((((False ∨ (True → (p4 ∧ (False ∨ False)))) ∧ (p2 ∨ (p3 → p2))) ∧ ((True → (p2 ∨ p1)) ∨ (p5 ∧ p2))) → ((p5 ∧ p3) ∧ (p5 → p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h10
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h21 := h7 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- False on the left can always be used.
    apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h35 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h37 := h33 h36
        -- We need to get the right conjuct of h37 based on <expert-advice>.
        let h38 := h37.right
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
          -- False on the left can always be used.
          apply False.elim h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h44 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h45 := h33 h44
        -- We need to get the right conjuct of h45 based on <expert-advice>.
        let h46 := h45.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- False on the left can always be used.
          apply False.elim h47
        case inr h48 =>
          -- False on the left can always be used.
          apply False.elim h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h50 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h51 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h52 := h33 h51
        -- We need to get the right conjuct of h52 based on <expert-advice>.
        let h53 := h52.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h54 =>
          -- False on the left can always be used.
          apply False.elim h54
        case inr h55 =>
          -- False on the left can always be used.
          apply False.elim h55
      case inr h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h59 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h60 := h33 h59
        -- We need to get the right conjuct of h60 based on <expert-advice>.
        let h61 := h60.right
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- False on the left can always be used.
          apply False.elim h62
        case inr h63 =>
          -- False on the left can always be used.
          apply False.elim h63
  -- Implications on the right can always be decomposed.
  intro h64
  -- Conjunctions on the left can always be decomposed.
  let h65 := h1.left
  let h66 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h67 := h65.left
  let h68 := h65.right
  -- Disjunctions on the left can always be decomposed.
  cases h67
  case inl h69 =>
    -- False on the left can always be used.
    apply False.elim h69
  case inr h70 =>
    -- Disjunctions on the left can always be decomposed.
    cases h68
    case inl h71 =>
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h72 =>
        -- One of the premise coincides with the conclusion.
        exact h64
      case inr h73 =>
        -- Conjunctions on the left can always be decomposed.
        let h74 := h73.left
        let h75 := h73.right
        -- One of the premise coincides with the conclusion.
        exact h74
    case inr h76 =>
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h77 =>
        -- One of the premise coincides with the conclusion.
        exact h64
      case inr h78 =>
        -- Conjunctions on the left can always be decomposed.
        let h79 := h78.left
        let h80 := h78.right
        -- One of the premise coincides with the conclusion.
        exact h79



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232010884814325325169612708232 : (((p2 ∨ p5) → True) → ((((p2 ∧ ((((p4 ∨ (((True → (True ∧ True)) → (p4 ∧ p1)) ∨ p3)) ∨ p2) ∧ True) ∧ True)) → p1) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207973120345545904795259694725 : ((((p3 ∨ p5) ∧ p4) ∨ (True ∨ True)) → (((((p1 ∨ True) ∨ (False ∨ p3)) ∨ p4) ∧ (p3 → (True → ((p4 → False) ∨ (True → True))))) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53888946247034917795019257538 : (((True ∧ ((p1 → p3) ∨ (((p2 ∧ p1) → p5) → p4))) ∨ ((((p1 → (p3 → p4)) ∧ p2) ∧ p5) ∨ ((p2 → p1) ∨ (p4 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41198670655454005537517840853 : ((((True ∧ (p5 → (((p4 ∨ p1) → (p4 → (p1 → (p3 ∨ p5)))) → (p3 ∨ ((True ∧ p2) ∨ p2))))) → ((True ∨ p3) → p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164873183063014761041625244760 : (((True → (((((True → p1) ∨ p5) → p4) ∨ (((p1 ∧ p4) ∧ False) ∨ p2)) ∨ p1)) ∨ False) ∨ ((p5 ∨ False) ∨ (p2 → ((p3 ∧ True) ∨ True)))) := by
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
theorem thm_5_vars_168970932298112762922575184672 : ((False → (((p1 ∨ (p2 ∨ (p3 ∧ p2))) ∨ p3) ∧ (p4 ∧ (((True ∨ p5) → True) ∨ p2)))) → ((False ∨ (((p1 ∧ p5) ∨ p1) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55221063827932782124706512846 : ((((p5 ∧ (p2 ∧ p5)) ∨ (p2 ∨ p1)) ∨ (((False ∨ ((((p3 → (True ∧ p2)) ∨ p3) ∧ (False ∨ (p5 ∧ False))) ∨ False)) → False) ∨ p3)) ∨ p1) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158433727445658096107635810944 : (((False ∨ p4) ∨ (((p3 ∧ (p1 → p3)) → (p3 ∨ (((p2 → p1) ∧ False) → (p2 → p4)))) ∧ p5)) ∨ (False ∨ (p1 → (p4 ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722477101634824176512696659779 : (((((p1 ∨ True) ∧ p2) ∧ ((False ∨ (p1 → ((p2 ∨ (p4 → False)) → (((((p1 ∧ (True ∨ p1)) → p5) ∧ p4) ∨ False) ∧ p3)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53166840508236030307087480195 : (((((((p1 ∨ p4) ∨ (p2 ∨ (p5 ∨ True))) → p2) ∧ p3) → p1) ∨ ((p1 ∧ ((p4 → ((p2 ∧ p4) ∨ p4)) → (p3 → p1))) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180995453445251631411652339712 : (((p4 ∧ False) ∨ ((p4 → False) ∧ (((p3 ∨ p5) ∨ True) ∨ (p5 ∧ p5)))) → (True ∧ (((False → p1) ∧ (p4 → (False ∨ (p2 ∨ False)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h13 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h14 := h6 h13
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
          -- Implications on the right can always be decomposed.
          intro h17
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h18 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h19 := h6 h18
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h24 := h6 h23
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h28
      -- False on the left can always be used.
      apply False.elim h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h30 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h31 := h6 h30
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309682294947864372436743492288 : (p2 ∨ (((p2 → (((p1 → (((True ∧ ((p2 ∧ p4) ∨ p3)) ∨ (False ∧ False)) ∧ (p2 ∨ p1))) ∧ False) ∨ p3)) → False) → ((p4 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160776522895508263720390742190 : (((p1 ∨ (((p2 → p2) ∨ p5) → p3)) ∧ ((((p5 ∨ p5) ∨ p5) ∨ (True → p2)) → (p2 → p5))) → (p2 → (p5 ∨ (p2 → (p1 ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : (((p5 ∨ p5) ∨ p5) ∨ (True → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h8
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303920225120895270037303738555 : (p1 ∨ (((((p5 ∧ p4) ∨ ((p3 ∧ p1) ∨ (p3 ∧ p1))) ∨ p3) ∨ (((p2 ∧ p5) ∨ p2) ∨ ((False ∨ p2) ∨ (p3 → (False → False))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225420105217036985423920396439 : (((p3 ∨ p1) ∧ p5) ∨ ((p1 ∧ ((p5 → ((p2 → (p3 ∨ p2)) ∧ True)) ∧ False)) ∨ ((p1 → (False → p5)) ∨ ((p3 → p1) ∨ (p5 ∧ p3))))) := by
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
theorem thm_5_vars_768902821032532168960818645882 : (((p5 ∧ ((((False ∨ p5) ∧ False) ∧ p5) ∨ (True ∧ (p5 → (((((p3 ∧ p3) → (False ∨ ((p4 ∧ p5) ∨ True))) → p3) ∨ p2) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299023185544078615479004963965 : (False ∨ ((p2 ∨ ((p2 ∧ p2) → (p4 ∨ (False ∨ ((((p4 → (True ∨ (p4 → p1))) ∨ p2) → False) ∨ ((True → False) → (p4 ∧ p2))))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134198496813775068132001345599 : (((((p5 ∧ p3) ∧ (False ∨ ((p4 → (p2 ∧ True)) → p3))) ∨ (True ∨ (p2 → (p5 → ((False ∧ p3) → p5))))) ∨ True) ∨ ((p3 ∨ True) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171836282231321515920729601953 : (((((p4 ∨ p5) ∧ p3) → ((p4 ∨ p1) ∨ (p1 → (p3 → (p2 ∨ False))))) → p5) ∨ ((((True → (p1 ∨ p4)) → p5) → p3) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185314579221007183103113598050 : ((p3 ∧ ((p2 ∨ ((p2 ∨ p4) ∨ (p3 → (p5 → True)))) → p5)) ∨ ((False ∨ p5) → (((True ∨ ((True ∧ p4) ∨ False)) ∨ False) ∨ (p3 ∨ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132697478849083922608159414166 : ((False ∨ ((p2 → p5) → ((p1 ∧ (((p1 ∨ ((((p4 → p4) ∧ p4) → True) → p2)) ∨ (p3 ∧ p5)) → False)) → p3))) ∧ ((p3 ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∨ ((((p4 → p4) ∧ p4) → True) → p2)) ∨ (p3 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68837839986119805232202841046 : ((p4 → ((p5 ∨ True) ∧ (((((p3 ∧ (p2 ∨ False)) → (p3 ∧ True)) → (p3 → p5)) ∨ ((p1 → p4) ∨ (p1 ∨ p1))) ∧ (p5 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697033758799288174349633919665 : (((((p2 ∧ (((p2 ∧ p4) → p3) ∨ p2)) ∨ ((p2 ∧ p4) ∨ p4)) ∧ ((((p5 ∨ False) ∧ ((False ∨ p5) ∧ p1)) ∨ p4) → (False → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190434323475384689882846000195 : (((p5 ∨ (p4 ∨ (False ∨ ((p5 ∧ p1) ∨ False)))) ∨ False) ∨ (((p1 ∧ ((False → p5) → p1)) ∨ p4) → (False → ((p4 ∨ p4) ∨ (p1 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



