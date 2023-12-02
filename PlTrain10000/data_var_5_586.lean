variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254837472941209839754822890095 : ((p3 ∧ p5) → (((p1 ∨ ((True ∧ p2) → ((p2 ∨ (False ∨ (p1 ∨ p2))) → False))) → p2) ∨ ((p1 ∧ (True → p5)) ∨ ((True ∨ p2) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_185741934571150747990369574260 : ((p3 → ((p2 ∨ (p2 ∧ p5)) ∨ ((p1 ∧ False) ∨ (p5 ∧ False)))) ∨ (p3 ∨ (((True ∨ (p4 ∨ p5)) ∨ False) ∨ ((p2 ∨ p3) ∨ (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65235789891459768688304186171 : ((p3 ∨ ((((((p4 ∧ p5) ∨ (True ∨ True)) → (p3 → ((True ∨ (p1 ∧ (False ∨ p5))) ∧ (p2 → (True ∧ p5))))) → True) ∧ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337120031899998897163511326109 : (p1 → ((True ∧ (p3 ∧ (((((p3 ∨ p2) ∧ ((p5 ∧ True) ∨ (((p2 ∨ p3) → p2) → True))) → p3) ∨ (False ∧ p1)) ∨ p2))) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4235042951700412820153235504 : (p5 ∨ ((p5 ∧ ((p3 → p3) ∨ p4)) → (True ∧ ((((((p2 → p5) ∧ (p2 → False)) → (p3 ∨ (p2 ∧ p3))) ∨ p3) ∧ p5) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147545584741773934418635479813 : (((p3 → (p5 ∨ ((False → (p3 → (((False → True) ∨ (p1 → (p5 ∧ p1))) → p4))) → (False ∨ p2)))) ∨ p5) ∨ (p2 ∨ ((p2 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50222016831875285599172473894 : ((((True ∧ (((False ∧ p2) ∨ (p3 → (((p3 → False) ∨ (p2 ∨ True)) ∨ (p4 → p1)))) ∧ p3)) ∨ p3) ∨ (p5 → ((p5 ∧ p5) ∨ p2))) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59903897393819567691440546946 : (((p5 ∧ p1) → (((False ∧ p5) ∧ ((p1 ∨ True) ∧ False)) ∨ ((True ∧ (p1 → (((p1 → (p3 → False)) ∨ p3) ∨ p2))) ∨ (False ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134655245014936148777587734512 : (((((p4 ∨ (p1 ∨ (p4 → (True → (p3 ∧ p1))))) ∧ p3) ∧ (((p5 ∨ (p5 → False)) ∨ p3) ∨ (p3 ∨ p5))) → p4) ∨ (p5 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113262989038825522802266377009 : ((((p5 ∨ (p1 → ((p2 ∨ ((p5 ∧ (p2 ∨ ((p2 → True) ∨ p3))) ∧ p3)) ∨ p2))) ∧ (p5 → (p4 ∨ p1))) ∧ (p5 ∨ p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178567390316504669198848771132 : ((((p3 ∨ p1) ∨ (p2 → (p2 ∨ p2))) ∧ (((True → p4) ∨ p2) → p1)) ∨ ((p2 ∧ ((True ∨ True) ∧ ((True → (p5 ∨ True)) → False))) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True → (p5 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (True → (p5 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339630779864018651911591962919 : (p1 → (p2 ∨ ((((p5 ∨ p4) ∧ p3) → p2) ∨ (True ∧ (((p4 → True) → p5) ∨ (p4 → ((p3 ∧ (p1 → False)) ∨ ((p2 ∨ p2) ∨ p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_225985587410781101761023899077 : (((p3 ∧ p4) ∨ p2) ∨ ((((p3 → (((p3 → False) ∨ p5) ∨ p1)) ∨ (p4 ∧ (p2 ∧ p4))) → p3) ∨ ((p4 → (p2 → (True ∨ p5))) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309825276476751654399802503152 : (p2 ∨ (((((p4 ∧ (True ∨ ((p5 ∨ p5) → (p4 → p5)))) ∨ (p3 ∨ p1)) ∨ (p2 → (p1 ∧ p5))) ∧ p3) → ((False ∨ True) ∨ (True ∨ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113493188156977498132878669511 : ((((((p1 ∧ p3) ∧ (p2 ∨ p5)) → ((p1 → (True → ((p4 → p3) → False))) ∨ p5)) ∧ (False → (p2 ∧ p2))) ∨ (p2 ∧ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244799527362858642482903039949 : ((p1 ∧ p1) ∨ ((True → ((p3 → ((p3 → p1) ∨ ((p3 ∧ p3) → (p5 ∧ (p5 ∨ ((p4 ∧ p4) ∨ p2)))))) ∨ ((p4 ∧ p5) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37647052406750769960834487960 : (((((p2 → ((((((p1 ∧ p5) → p5) ∧ True) ∨ p3) ∧ ((p1 ∧ p1) → (p4 → (p5 ∧ (p5 → p2))))) ∧ p2)) ∨ False) → p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198854702701505478219320268874 : ((p2 → ((((p1 ∧ False) ∨ p1) ∧ p1) ∨ p4)) ∨ ((p5 → True) ∨ (p3 ∨ (((True ∨ p1) → (((p4 ∨ (p4 ∨ True)) ∧ p3) → True)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46583277190597380788489805045 : (((False ∧ ((True ∧ (((((p2 ∨ p2) ∧ ((False → p2) ∧ True)) → (p2 ∨ (p5 ∧ p3))) ∧ p1) → p4)) → (p4 → p2))) ∧ (p2 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681980472987894204516940770845 : (((((((p2 → ((True → p1) → p5)) ∧ (False ∧ False)) ∨ ((p2 ∧ (p5 ∧ p2)) ∧ p4)) ∨ p1) ∧ (p5 → (p3 → (p2 → (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358519637089738673568204337263 : (p5 → (p2 → ((((p5 → ((((p4 ∧ False) ∨ p5) ∨ (p3 ∨ p3)) ∧ p3)) → (((False ∧ p3) ∧ p5) → (True ∨ (p3 ∧ p1)))) → p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612087761061800103174236346799 : (((((((((((p3 ∨ p3) → ((True → (p2 → False)) ∨ True)) → p1) ∧ True) ∨ p3) ∨ (p5 ∨ p5)) → (p3 ∧ p2)) ∧ (p2 ∨ p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344850913398032496092002793232 : (p2 → (p5 → ((((p5 ∧ (p2 ∧ p2)) ∨ (((p2 ∨ True) ∨ True) → (p1 → p2))) → ((p4 ∨ True) ∧ False)) ∨ (p5 ∨ ((p2 ∧ p4) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310147755176871727720542794713 : (p2 ∨ ((((True ∨ p2) → ((p3 ∨ ((True ∧ (p3 → p4)) → p3)) ∨ False)) → p2) → ((p1 ∧ ((False ∧ p1) ∨ p2)) ∨ (p2 ∨ (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164789885347348267352645576098 : (((((True ∧ (p4 ∧ p5)) ∨ p2) ∨ (((p1 → p3) ∧ (p4 ∨ (p1 → False))) → p5)) ∨ False) ∨ (True ∨ ((p2 → (p5 ∨ (p2 ∧ p5))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168587014731379636885491210816 : ((p2 ∧ ((p4 ∧ p2) ∨ (True ∧ (p1 → ((p4 → p5) → (p1 ∨ (p3 → (False → p4)))))))) → (p5 → ((True → (False ∨ (p2 → False))) → p1))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587356282606896657844206324702 : ((((((p4 ∧ (((p4 ∧ (True → p3)) → p5) ∨ ((p1 ∨ (False ∨ False)) ∧ ((False ∧ (False ∧ p5)) ∨ (True ∧ p5))))) ∧ False) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184747207057377508895015545748 : ((((True → (p2 → True)) → True) ∧ (((p1 ∧ p4) → True) ∧ p2)) ∨ (((True ∧ ((p4 → p5) ∧ (False ∨ p1))) ∨ ((False ∧ p4) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107163825593237650046036700192 : ((((p4 ∨ p1) ∨ True) ∧ (((False ∧ p2) ∨ p3) → (((False ∨ (p1 ∧ (False → (True ∧ (p2 ∧ (True → p2)))))) ∧ False) ∨ True))) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42854028880485880351480214894 : (((p2 → ((True → (((p1 → False) → True) ∧ ((((((True ∨ (False → p2)) → p4) ∧ False) ∧ p4) ∧ False) ∧ True))) → (p3 ∨ p3))) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197650919085839593631605461292 : ((((p2 ∨ (p5 ∧ p1)) → p4) → (p3 ∧ False)) ∨ (p2 ∨ (((p1 ∧ True) ∧ (p2 ∧ False)) → (p4 ∨ (p2 ∧ ((p5 → (p3 → p1)) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_64526202027319221478212996122 : ((p1 ∨ ((((p4 → True) → p3) → (p1 ∨ ((p3 ∧ p1) → False))) → (((False ∨ p1) ∧ ((False → ((p3 → p5) → True)) ∧ p5)) → p5))) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732665329103600353637696385061 : ((((p1 ∧ p2) ∧ (p4 ∧ (True ∧ (((p2 → (p3 ∧ (p3 → False))) ∧ ((((p4 ∨ p5) ∨ p2) ∧ p1) ∨ (False → (p2 → p1)))) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113136473480769001512956313887 : (((p2 → ((((p4 → False) ∨ ((p3 → (p3 → (p2 ∧ p4))) ∧ p1)) ∨ p1) ∧ ((((p2 ∧ p4) ∧ p4) ∨ p3) → p1))) → p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219231892089110184131690441445 : ((p1 ∨ ((p5 ∧ p1) ∨ p2)) → (p2 ∨ ((p5 ∨ ((p1 ∧ (((p3 ∧ p4) → p5) ∧ p2)) ∧ (p4 ∨ p4))) ∨ ((False → (p2 → p5)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358079444574903549201303413680 : (p5 → (p1 ∨ (p2 ∨ (p2 ∨ ((((((True ∨ (False → p2)) ∧ (((p2 ∨ (True → p5)) ∧ p1) ∧ p5)) ∧ p4) → (p3 ∨ p2)) → p3) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698254797644737098588850191339 : (((((p4 ∨ ((p2 → ((p1 → False) ∧ False)) ∨ (p5 ∨ p3))) → p5) ∨ ((p1 ∧ ((((p1 ∧ (False ∧ p1)) ∨ False) ∨ False) ∧ p3)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52004029445412076569590781340 : (((p1 ∧ (p1 ∧ (p5 ∨ (((p4 ∧ (p1 ∧ ((p3 ∨ p1) ∨ True))) ∨ p2) ∧ p3)))) ∨ ((False → ((p2 ∨ p5) ∨ (p4 ∧ p1))) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184238765894617020185485000843 : ((((((p4 → p2) ∧ ((p3 ∧ True) ∨ p5)) → p3) → p4) → p2) ∨ (((p1 ∨ (p4 ∨ (p2 ∨ p4))) ∨ p3) → (True ∨ (p2 ∨ (p3 ∨ False))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
theorem thm_5_vars_67331654882459200790951534115 : ((p1 → (((p4 ∨ (((p3 ∧ p5) → (p1 → (p3 ∨ (((False → False) ∧ False) → (p1 ∧ (False ∨ (False ∨ p2))))))) ∧ p3)) → p4) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232985344166221300105284842709 : ((p3 ∧ (p3 → p1)) → ((False ∨ (((p2 → ((p2 → (p3 → (True → ((p2 ∨ (p5 ∧ True)) ∨ p2)))) → p5)) ∨ (False → p5)) → p4)) ∨ True)) := by
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
theorem thm_5_vars_172407862553818257901577214571 : (((((p2 → p3) ∨ True) ∧ p5) ∧ ((p1 ∧ True) ∨ ((p2 ∧ p5) ∧ (p3 ∧ p1)))) ∨ ((((True ∨ p2) ∨ True) ∨ False) → (False → (p2 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153220101582507838551227141601 : ((True ∨ ((p5 ∧ p2) ∧ ((p3 ∨ ((False → (p4 ∧ ((True → p1) ∨ (p4 ∨ False)))) ∨ p5)) ∧ (p4 → p1)))) → ((p4 ∧ p2) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299221206380997429328949168558 : (False ∨ (((p5 → (p2 ∧ ((p2 ∨ ((True ∧ (p4 ∧ (p2 ∨ (p1 → ((p1 ∨ p4) → False))))) → (p4 ∧ False))) ∧ p2))) ∨ (False → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225828500834205585691689777424 : (((True ∧ p4) ∨ p2) ∨ (p5 ∨ (((p2 ∨ False) ∨ (True ∧ (((p4 ∧ p3) ∧ (p5 ∧ (p2 → p5))) → ((p4 ∨ p5) → p4)))) ∧ (False → p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h17
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119048999635925793138467795016 : ((p1 → (((True ∨ (p2 → (p3 → ((False ∧ p1) ∧ (p3 ∧ p1))))) ∧ (True ∧ ((p4 ∧ ((p3 ∨ p3) → p3)) → False))) ∨ False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4251147234664620145334183627 : (p5 ∨ (p2 ∨ ((p4 ∨ (p3 ∨ p5)) ∨ (p1 ∨ ((False ∨ (True ∨ ((p5 ∧ (p5 → ((True → p4) ∧ p2))) ∨ (p5 → p1)))) ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588853775912635799980044367800 : (((((p1 ∨ (p3 ∧ (((p4 ∧ (p2 → (p3 → (p5 → ((False → p2) → True))))) ∧ True) ∧ ((p3 ∨ (p4 ∧ False)) ∨ p4)))) ∨ p1) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58144395052917526906802458041 : (((p2 ∧ p3) ∧ ((p1 ∧ p4) ∧ (p4 ∨ (True ∧ ((((p4 → p3) → (((True ∨ (p2 → p1)) ∧ p4) → p3)) ∨ p1) → (True ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855521228451988350155577199414 : (((((((p5 ∨ p1) ∧ ((((p3 → (p5 ∧ (p4 ∨ (False → p4)))) → p2) ∧ True) ∧ (False ∧ (p2 ∨ (True → p3))))) ∧ False) ∨ True) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ p1) ∧ ((((p3 → (p5 ∧ (p4 ∨ (False → p4)))) → p2) ∧ True) ∧ (False ∧ (p2 ∨ (True → p3))))) ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353715803879433115449566120618 : (p4 → (True → (((((True ∧ True) → (True ∨ (p5 ∧ (True ∨ p2)))) ∧ (p2 → False)) → (p3 ∨ (((p2 ∧ False) ∨ True) → (p3 ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324644259835195553356858171888 : (p5 ∨ (((False ∧ p2) ∨ p2) ∨ ((((True ∨ ((((p5 ∨ False) ∨ (p2 ∨ (((True ∧ p4) → p5) ∨ p5))) ∨ False) ∨ p1)) ∧ True) → p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ ((((p5 ∨ False) ∨ (p2 ∨ (((True ∧ p4) → p5) ∨ p5))) ∨ False) ∨ p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316975836199146007763929268450 : (p3 ∨ (p3 → ((p1 ∧ ((((p4 ∧ (p4 → (((p4 → (p1 → False)) ∨ (p3 ∧ (p1 → p4))) ∧ p4))) ∨ (p4 ∧ True)) ∨ True) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731553496852801583659766984035 : ((((False → (True → True)) → (((p2 ∨ ((p2 ∧ (True → ((p3 ∧ True) → False))) → p1)) → (p1 ∨ (p1 ∧ ((p2 ∨ True) → False)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148655791373381478291412131902 : ((((p1 → p2) ∨ (((p1 → p3) ∨ p4) → p1)) ∧ ((((p1 ∧ p4) → False) → (p1 ∧ (p4 ∧ p2))) → p1)) ∨ ((p2 ∨ (p4 → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305005834469693193613223842976 : (p1 ∨ ((((False ∨ p4) ∨ (p1 → (p2 → (p2 ∨ (False ∨ (p5 ∧ p2)))))) → ((p1 ∨ (p3 → (p3 → p5))) ∧ p3)) ∨ ((p2 ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695269471513875744592055678785 : (((((((p5 ∧ (p5 ∨ ((p2 ∧ False) → p3))) ∨ False) ∧ (p5 ∨ p2)) → p4) → ((p1 ∨ False) ∧ (((p2 ∧ (p4 ∨ p2)) → p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674851996360882020292136680337 : ((((p5 → (False → ((p4 ∧ False) → ((p2 ∧ (p4 → True)) ∨ ((((p3 ∧ (True ∧ p2)) ∧ False) ∨ False) ∧ p1))))) → ((p4 → p5) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136391756288308357834325439447 : (((p2 ∧ ((p1 ∨ True) ∨ p2)) ∨ (((True ∧ p5) ∨ ((p5 → ((p1 → (p5 ∨ p2)) ∧ p1)) ∧ (p3 → p1))) ∧ False)) ∨ ((p1 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765349543370083832465283068846 : (((p4 ∧ ((((True ∧ ((p5 → (True ∨ p3)) ∨ p3)) ∧ (p5 ∨ ((((True → True) ∧ True) ∧ p4) → False))) ∧ p3) → (p5 ∨ (False ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735437329935162207242623000652 : ((((p4 ∨ p3) ∧ ((((p1 ∨ False) → (p1 → ((p2 → (((True ∧ False) → p2) ∧ ((p1 ∧ False) ∨ p4))) ∧ True))) → (p3 → p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111654403251339936496570287609 : (((((False → p2) → (p3 → (((p4 ∧ p2) ∨ ((p5 → p4) ∨ ((p2 ∧ False) → (p1 ∧ True)))) ∨ (p2 → p5)))) ∨ p2) ∨ p1) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142318065615052587936572517728 : ((p3 ∧ ((((True ∧ (((((True ∨ ((False → p5) ∧ p4)) ∧ True) → p5) → p1) → (p3 ∧ p5))) ∧ p3) ∨ p2) → p3)) → ((p3 → p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304765534706887693632089948247 : (p1 ∨ ((p4 ∧ (((((p2 ∨ ((((p3 ∨ True) ∨ (p3 ∧ p4)) → p5) ∨ ((p3 ∨ p2) ∨ False))) ∧ p1) ∨ p3) → p4) ∨ p3)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148705685079694098990203041050 : (((((((p2 ∧ p5) → p1) ∧ p4) ∨ p1) → True) → ((((p1 ∧ p3) ∧ p1) ∨ (False → True)) → (p3 ∨ False))) ∨ ((p4 → p4) ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625030577460920650750168185398 : ((((True → (((((False → p2) → (False ∨ p3)) ∧ p2) ∨ ((((False ∨ p1) ∧ ((p4 → p3) → (False ∨ True))) → True) ∧ p1)) ∧ p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358219975227101458124297285571 : (p5 → (p4 ∨ ((p1 → ((p4 ∧ p4) ∨ (False ∧ (((p4 ∧ (p3 → (p3 ∨ ((p5 ∨ p3) ∧ False)))) ∧ p4) → (True → (False ∨ p5)))))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762940492067547130394155775845 : (((p3 ∧ ((p2 ∧ ((p3 ∨ p1) ∨ p3)) ∧ ((((p2 → p2) ∨ p1) ∨ (((p2 ∧ p5) ∧ ((p2 → p3) → False)) → (p5 → p5))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636593901154755205414208475635 : (((((True → (p5 ∧ (True → (p4 ∧ ((p3 → (p1 → p4)) → (p5 ∧ p4)))))) ∧ (True ∧ (False ∨ ((True ∧ (p2 → p1)) → p2)))) → p4) ∨ p3) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44395635252203337394086770437 : ((((True ∨ (((((((False ∨ True) ∧ p5) → p3) → p2) ∨ False) ∧ p4) → p5)) ∨ (((p4 ∨ ((p4 ∧ p1) ∨ p4)) → p5) → True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217339006378900998748286827601 : (((p1 ∨ (p3 ∨ p3)) ∨ p3) → (((((p5 ∧ p1) → ((p1 ∧ p3) → p3)) ∧ (p3 ∨ False)) ∧ (False ∧ p1)) ∨ (((False → p2) ∧ p1) → p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h6
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
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777267020097208309636626674918 : (((p1 ∨ (((True ∧ ((p4 → (p3 → True)) → (True → ((p4 → p4) ∧ (p4 ∨ p4))))) ∧ ((p5 ∧ p5) ∧ p5)) → ((p4 ∨ p2) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190025671736411635196789897473 : ((((False ∨ (p3 ∨ (p4 ∨ (p2 ∧ False)))) ∧ p5) ∧ p4) ∨ ((((False → p2) ∨ True) ∨ False) ∨ (((p1 ∨ p2) ∧ (True ∧ p3)) ∧ (p3 → p5)))) := by
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
theorem thm_5_vars_134807262418004865402601111804 : (((p5 ∧ (((False ∨ (p4 → p4)) ∨ (False ∧ ((p3 ∨ p2) ∧ ((False → (p1 → p3)) → False)))) ∨ (p2 → p5))) → False) ∨ (False → (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185573587530661338924196766983 : ((p4 ∨ (p1 → ((True ∧ False) ∨ (((p5 ∧ p4) → p2) ∧ False)))) ∨ ((p5 → False) → ((p1 ∨ (p1 ∨ ((p2 → (True ∧ p4)) ∨ True))) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626566938776512534969244053754 : ((((p4 → (((p1 ∧ p1) ∧ p2) → ((p3 ∧ p3) ∨ (((p1 ∨ p2) ∧ p5) ∨ ((p2 ∨ (p5 ∧ ((p3 → True) ∨ p2))) ∧ False))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157164733711341303553247751011 : ((((p4 → ((p1 → (p5 ∧ True)) ∨ (((False ∧ (p5 → p5)) ∧ (p5 ∧ p3)) → p5))) ∨ True) → p3) ∨ ((p1 ∧ ((p2 → p4) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_845054279080323299053718602083 : ((((((p3 ∧ p3) → (p5 → p5)) → ((((p5 ∧ (p2 ∧ False)) → p5) ∨ p5) ∧ ((p2 ∨ (p3 → p5)) ∧ ((p5 ∨ p2) ∧ False)))) ∨ p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p3 ∧ p3) → (p5 → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h3
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38792586503662971275152610516 : ((((p4 ∧ (False ∨ (p5 ∧ p3))) ∨ ((True → p1) → ((p4 ∧ ((((p3 ∧ p1) ∨ (True → p2)) ∧ False) ∨ (p4 → p3))) → p4))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709564095061982605344662410536 : ((((False ∨ (((False → p4) ∨ p1) ∨ (p2 ∨ True))) → ((p1 ∧ ((p5 ∧ p2) ∧ False)) ∨ ((p1 → (p2 ∨ True)) ∨ (p4 ∧ (p5 → p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
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
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147733853645082576872732983216 : ((((((p2 ∧ p2) → p4) ∧ p5) ∧ (((((False ∨ p1) ∨ p1) → (p4 ∨ (p1 ∧ True))) ∨ p4) → p4)) → False) ∨ ((True → p1) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346591931257603925254770598038 : (p3 → (((((p5 → p4) ∧ (False ∧ False)) ∨ ((p5 ∧ ((((False → p1) ∨ p1) ∨ p3) ∧ (p1 → p5))) ∨ p3)) ∨ p4) ∨ (p3 ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134767774567581671171787575315 : ((((p5 → p5) → (((((p5 → ((p3 ∧ False) → (p4 ∨ (p3 ∧ p5)))) ∧ p5) ∧ p4) ∨ p5) ∨ (p2 ∧ p3))) → p3) ∨ (p5 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87398886233927883746493387334 : (((p4 ∧ ((p3 ∨ (p2 → p4)) → False)) ∧ ((((p5 → ((True ∨ ((True ∧ p4) → (p3 → False))) → p5)) ∨ (True ∧ p3)) ∨ p4) ∧ p4)) → False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : (p3 ∨ (p2 → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p3 ∨ (p2 → p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : (p3 ∨ (p2 → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h21 := h5 h19
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57194586593514989919064300587 : ((((p3 ∨ p3) ∨ p5) ∨ (p4 → (p4 ∧ (((((((p3 → (p5 ∧ p1)) → ((True → p3) ∨ p3)) ∨ True) → p2) ∧ p5) ∨ p4) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58598064453785608492180614192 : (((False → False) ∧ (((p5 → p4) ∧ (((True ∧ p5) → p3) ∧ (((((p4 ∨ p4) → p5) ∧ (p3 → p1)) → False) ∧ p3))) ∨ (p4 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171683400638849299235493949697 : (((p3 ∨ (((p1 ∧ ((True ∧ p4) → p2)) → (p2 ∧ p1)) ∨ (True ∧ p2))) ∨ p2) ∨ (((p3 ∨ False) → False) → (p2 → ((p4 ∧ p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203832760681402642448471954081 : ((False → ((True → (True → p4)) ∨ p4)) ∧ ((p2 ∧ (p4 ∧ p2)) → (((p5 ∨ (p3 ∧ p3)) ∨ p2) ∧ (((p2 ∧ p1) → p5) ∨ (p5 ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191779193657933089944530707311 : ((p1 ∨ ((p5 ∧ p5) → (((False → p1) ∧ p3) ∨ False))) ∨ (p5 ∨ (p4 → (p2 → ((((p1 → p4) → (p2 ∨ p4)) ∧ p3) ∨ (False ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_160522006657474946311740234210 : ((((((((p5 ∨ p1) ∧ False) ∧ (False → p4)) ∧ True) → True) ∨ p4) ∨ ((p4 ∨ p5) ∧ (p5 ∨ False))) → (p3 ∨ (((p5 ∧ True) ∧ p1) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157903376869887052647868742992 : ((((p2 ∧ (p1 ∧ (True ∨ ((p3 ∨ p5) ∧ True)))) → p4) → ((p4 ∨ (p2 → True)) → (p3 → p1))) ∨ (True ∨ ((p4 ∧ p2) ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231064041568703193278146974322 : (((True ∨ p4) ∨ p3) → ((((((False ∨ (p1 ∨ (p5 ∨ p1))) ∧ (p4 → (False → p2))) ∨ p3) ∨ p3) ∨ False) ∨ (p2 → ((True → True) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63262102231903589634901846250 : ((p5 ∧ (((p5 ∨ ((p1 → p3) ∧ p2)) ∧ p2) ∧ (((p3 → ((p3 ∧ ((p2 ∨ ((p1 ∨ p1) → p4)) ∨ p5)) ∨ p2)) ∧ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51446076323164432548288302954 : (((((p5 ∨ ((True ∧ False) ∨ (p3 ∨ p3))) ∨ (p1 ∨ (p4 ∨ True))) ∧ ((True ∨ False) ∧ p2)) → ((p4 ∨ ((p4 → p2) ∨ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55042964835820927625314851140 : (((p5 ∧ ((p1 → p4) → (p1 ∨ p5))) ∧ (p2 → ((p5 ∨ (p2 ∨ (p4 ∨ p1))) ∧ (((p2 ∧ (p1 ∧ p4)) → (p2 ∨ p2)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136680801181123419382293493507 : (((p1 → (False → False)) → ((((((p2 → p3) ∨ p3) → (p4 ∧ ((p3 ∨ p2) → p5))) ∨ (False → p4)) ∧ p2) ∨ True)) ∨ (p5 ∧ (True ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139018703782405349317738333689 : ((((p4 → ((((False ∨ (p1 ∧ p4)) → True) ∨ ((p1 → p3) ∨ (p5 ∧ p3))) ∧ (True → (p5 ∧ p5)))) ∨ p3) ∨ False) → (p5 ∨ (p3 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189611433152272497712916262052 : ((False ∨ (p3 ∨ (p3 ∨ (False → (p1 → (p5 → p1)))))) ∧ ((p2 ∧ (p5 → False)) → ((True → p5) → (p1 → (p3 ∧ (False → (p5 ∧ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h11 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151070158366880556913256280012 : ((((((p1 ∧ (((((True ∧ p5) ∧ False) → p3) ∨ p4) → True)) → p3) ∨ ((p2 ∨ p4) ∧ True)) ∨ p4) → p3) → ((p1 → p2) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172068952723630945796553265780 : (((((True → p3) ∧ ((p3 ∧ (p4 ∨ p4)) ∨ p4)) ∧ (p1 ∨ p5)) → (p1 ∧ p2)) ∨ ((p5 ∧ (p1 ∧ ((p2 ∨ True) → (p4 ∨ False)))) → p1)) := by
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



