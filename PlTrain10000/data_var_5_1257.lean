variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596700482991087929563088160734 : ((((((True ∨ p5) ∧ (p5 → (p5 ∧ p3))) ∧ (((((p5 ∨ (p2 ∨ p2)) ∨ p1) → (p1 ∨ True)) → p3) ∧ ((False ∧ p2) ∧ p2))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680551943771496931166198012917 : (((((((p3 ∨ (p1 → True)) ∨ p1) ∧ (p5 → True)) ∧ (p5 → (((p4 ∨ False) ∨ (p3 → p2)) → p5))) → (False ∨ (p5 ∨ (False ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
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
theorem thm_5_vars_41815721331073429330728803834 : (((((p5 → p3) ∧ p4) ∧ (((((((((p1 ∨ ((True ∧ True) → p3)) → p2) ∨ p4) → p5) ∧ False) → p5) → p3) ∨ p2) ∧ p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156620705584568926787676386727 : ((((((p2 ∧ True) ∧ (((p1 ∨ p1) ∨ False) ∧ ((p1 → p2) ∨ (p4 → p2)))) ∨ p5) ∨ True) ∧ True) ∨ ((False → False) ∧ ((p4 ∨ p4) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112224664470030449725529133251 : (((p1 ∨ ((p3 → p5) → ((((((p3 ∧ p4) ∨ p2) → p4) ∨ (p4 ∨ (p4 ∨ (p4 → (p1 ∨ True))))) ∨ p2) ∨ p1))) ∨ p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304748616479302383238630304712 : (p1 ∨ (((p2 ∧ False) ∧ (((p5 ∨ p3) ∨ ((p2 → True) ∧ (True → (False ∨ p4)))) → ((p3 ∨ p4) ∧ (p4 → (p4 → p3))))) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786815945774522157567121911387 : (((p4 ∨ ((False → ((p4 ∨ True) ∨ p5)) → (True ∧ (p4 ∧ ((((True ∧ p4) → p4) ∧ p1) ∧ ((p1 ∧ ((False ∨ p4) ∧ p1)) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185054426720361505783050477678 : (((True ∧ p4) ∨ ((p1 → False) ∧ ((p3 → (False ∧ p5)) → p4))) ∨ (((False ∧ ((p5 ∨ p4) ∧ True)) → ((False ∧ (p4 → p4)) → p1)) ∨ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609490602245322402498169675546 : (((((p1 ∧ (((False ∨ p5) → (((p5 ∨ p3) → ((True ∨ ((p3 ∧ (False → p2)) ∧ p1)) ∨ (p4 ∧ p3))) → p1)) → p1)) ∨ False) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246621112339367218828199262748 : ((p5 ∧ p3) ∨ ((p2 ∨ (((((p1 → p4) → True) ∧ ((False ∨ p1) ∨ ((p3 → (p2 ∨ True)) → p2))) ∨ (p3 → True)) ∨ (p5 ∧ False))) ∨ p1)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654231314300392753783962660025 : ((((((((p1 → True) ∧ ((False ∧ p4) → p3)) → ((((p3 → p1) ∧ (p5 ∧ p5)) → p1) ∧ (p2 ∨ p4))) → p3) ∨ p2) ∨ (p3 → p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66506663182976238881240542093 : ((True → ((True → (((p3 ∧ ((p5 → p3) ∨ ((p3 → ((p4 ∧ ((p2 ∨ p5) ∨ p1)) ∨ p3)) ∧ p4))) ∨ (p1 → p3)) → p5)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615065098467609435369056318258 : (((((p4 ∨ (((p5 ∧ p4) → (((False ∧ (((p5 ∧ p2) ∨ True) ∧ p2)) ∨ True) → p5)) → p5)) → ((p1 ∨ (p5 ∨ p4)) ∨ True)) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165852767585993579883555654749 : ((((p5 → False) → False) ∨ ((False ∧ ((p5 ∧ p4) → (p2 ∨ ((p4 ∨ p1) ∨ False)))) ∧ p5)) ∨ (p3 ∨ ((False → p1) ∨ (p4 ∨ (True → p4))))) := by
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
theorem thm_5_vars_172034537731385536144510256740 : (((p5 ∧ (((((p5 ∨ (p3 ∨ p4)) ∧ p2) → False) ∧ p5) ∧ p1)) ∨ (p3 → True)) ∨ ((False → ((True ∧ p3) → (False ∨ False))) ∧ (p2 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166970043764572613606732040423 : (((p3 ∧ ((p5 → ((p2 ∧ True) ∧ p5)) ∧ ((False → (p3 ∨ (p3 ∨ p1))) → p1))) ∧ p3) → ((((p1 → False) ∧ True) ∨ True) ∨ (p5 → p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47039923750976484306394840827 : (((((p3 ∨ ((True ∨ (True ∨ p4)) → ((p4 ∨ ((False ∨ p2) ∨ p4)) ∧ False))) ∨ ((True ∨ False) → p3)) ∧ (p3 ∨ p5)) ∨ (p2 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264663780934316309464604384439 : (True ∧ ((p5 → (p2 ∧ p2)) → ((((((False → p2) ∧ p3) ∨ True) ∨ ((p1 → (p1 ∧ ((p3 ∨ p3) ∧ True))) ∧ (p1 ∨ False))) → False) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((False → p2) ∧ p3) ∨ True) ∨ ((p1 → (p1 ∧ ((p3 ∨ p3) ∧ True))) ∧ (p1 ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114319602711638051255293373819 : (((((p3 ∧ True) ∨ p4) → (p3 ∨ ((True → ((True → p1) ∨ (p3 ∧ (False ∧ p1)))) ∧ p3))) ∧ (p5 ∧ (False → (False ∧ p4)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213323861242150910713299317687 : (((p1 ∧ (p4 ∧ False)) ∧ p2) ∨ ((p2 → (p3 → (p4 ∨ ((p5 → (p2 ∨ ((((p2 ∧ p3) ∨ p1) ∨ (p4 ∧ p3)) → p1))) → p3)))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52634841759271882585578434367 : ((((p3 ∧ p2) ∨ (((p1 ∨ p3) → (p3 → (p2 ∨ p4))) ∧ (p3 ∨ p5))) ∨ (p3 → ((False → (p5 ∨ (False ∨ False))) → (True ∧ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147406117579486770737053220123 : ((((p4 ∨ ((p4 ∨ p4) ∧ (p5 → p3))) → (((p5 ∧ p4) ∨ (True → ((p2 ∧ p1) ∨ False))) ∧ True)) ∨ p3) ∨ (((p3 → p3) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229422677714519443271685811151 : ((p1 → (True → p4)) ∨ (((p5 ∧ (p2 ∧ (p5 ∨ True))) ∨ ((((False ∨ p3) ∨ True) ∨ (((p1 ∨ (p2 ∨ p5)) → p2) → True)) ∨ p5)) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151596340401210665590065736589 : (((((p2 → p5) ∨ p3) ∨ (True ∨ ((((p1 ∧ p2) ∨ p1) ∧ True) → (p1 ∨ (p1 → p1))))) → (False ∧ True)) → (p2 ∨ (p4 ∧ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p5) ∨ p3) ∨ (True ∨ ((((p1 ∧ p2) ∨ p1) ∧ True) → (p1 ∨ (p1 → p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219550208347501001907381940598 : ((True → ((p2 ∧ p5) ∧ False)) → ((((False ∨ p3) ∨ ((p5 ∧ ((False → (p3 ∨ p1)) ∧ (True ∧ (p2 ∧ p3)))) ∧ p3)) ∨ False) ∨ (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68027635783986931098274461667 : ((p2 → (p1 ∧ ((p2 ∧ (((p1 ∧ ((p4 ∧ (True ∨ p5)) → p5)) ∧ True) → (True ∧ p5))) ∨ (((False ∨ p1) ∨ p1) → (False ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149180879755404346947704215826 : (((False → p3) ∧ (p2 ∧ ((True ∨ (p3 ∨ ((p4 ∨ ((p3 → (p1 ∨ p4)) ∧ (False → p4))) ∨ False))) → p4))) ∨ ((True → False) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746039835788934345435235424210 : ((((p1 ∨ True) → (((p5 ∧ p2) → (p3 ∨ False)) ∨ ((p5 → p4) → ((False ∧ ((True → p3) ∨ (p3 ∧ ((p5 ∨ p2) ∨ p5)))) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599308342902034540814405904790 : (((((p1 ∧ p1) ∨ ((p5 ∧ (((p4 ∧ (p5 ∧ ((p3 → (p4 ∧ (p2 → p4))) → True))) ∧ p3) → (p2 ∧ (p1 → p3)))) ∨ p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196554056964384067768971359556 : ((p3 → ((p1 ∨ p1) ∨ (p1 ∨ (p2 ∨ True)))) ∧ ((p1 → ((True → (p3 ∧ True)) ∧ p2)) ∨ (False → (p4 ∨ ((p4 ∨ True) → (True ∧ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354672346879878887322697327366 : (p5 → (((True → ((((p4 ∨ p2) ∨ (p5 ∧ ((p2 → p5) ∧ p3))) ∨ p4) ∨ ((((True ∧ False) → p2) → (True ∨ False)) ∧ p2))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201153866389522791995010971905 : ((False → ((p2 → p3) → (p2 → (p1 ∧ p1)))) → (((p5 ∨ ((p5 → p5) ∧ p5)) → ((False → True) ∧ False)) ∨ ((p4 ∧ p3) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600152882919491116969524852522 : (((((True → False) → (((p2 ∧ (p5 ∧ (p2 ∨ True))) ∨ (((p1 ∨ p1) ∧ ((((p3 ∧ p5) ∨ p1) → p1) ∨ False)) ∧ False)) ∧ p2)) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153509580118438600756602038647 : ((p5 ∨ (False ∨ (p2 → (((p2 → ((p2 ∧ (((p5 ∨ p1) → (p3 ∨ p2)) → True)) → True)) ∧ True) ∨ p3)))) → ((p1 → (p4 ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_111415495889989894184714023405 : (((p3 ∨ ((((p1 → ((p3 ∧ p1) → p2)) ∨ p1) ∧ (((p2 → (p2 ∧ p1)) → False) ∨ (p4 ∧ p5))) ∧ (p1 → False))) ∧ True) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40630458707965557069547751234 : (((((((True ∨ (p2 ∨ p4)) ∧ (((True ∧ p1) ∨ ((((p1 → p5) → p1) ∨ p1) → (False → p2))) → False)) → p2) → p3) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305775172931992963166851710410 : (p1 ∨ (((True ∨ p3) ∧ (False ∧ ((p1 → True) → p3))) ∨ (True ∨ ((((((((p2 ∧ p5) ∧ p3) ∧ False) ∧ p3) → p5) ∨ True) ∨ p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136941492031416028594913792627 : (((p4 → p3) ∨ ((p4 ∧ ((p3 ∨ (p1 → ((p1 ∧ p3) → p4))) ∨ (False ∨ (p1 ∧ p3)))) ∧ (p3 ∨ (p4 ∧ p5)))) ∨ (p3 → (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177790766788126231327674203974 : (((False ∨ ((((True → p4) ∧ (p5 → (p2 ∨ p3))) → False) ∨ True)) ∧ False) ∨ ((p2 ∧ p2) → (True ∨ (False ∨ ((p2 → p4) ∨ (p1 ∨ p2)))))) := by
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
theorem thm_5_vars_187394089708828412681028274543 : ((p4 ∧ (((((p1 ∧ p2) ∧ p4) → True) ∨ p4) ∨ (p2 ∧ p3))) → ((p5 → (((False ∧ (True ∨ p2)) ∧ False) ∧ p2)) ∨ ((False → False) ∨ p4))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325961451253860529714783627307 : (p5 ∨ (p5 ∨ (p3 ∨ ((((((((p1 ∨ False) ∨ p2) → (p1 → (p3 ∧ True))) → (p2 ∧ p1)) → True) → p3) ∨ p3) ∨ (False → (p3 ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624312710562453789251895665460 : ((((p3 ∨ ((p2 ∨ (p2 ∧ ((p3 ∨ p3) ∧ (False ∧ ((True ∨ (p2 ∧ True)) ∧ True))))) ∧ (((p3 ∧ p3) ∨ (p2 ∧ p3)) ∧ p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199641935837996628584771688214 : (((((p5 ∧ p3) ∧ False) → (False → p5)) → False) → (p5 ∨ (p2 ∧ (p4 ∧ (((False ∧ (p5 ∨ p5)) ∨ (p1 ∧ p2)) → ((p4 → p3) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p3) ∧ False) → (False → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55278362015203128580073264620 : (((True ∧ (p3 ∧ (False ∨ (p5 ∨ False)))) ∨ ((False ∨ ((((((p3 ∧ (p1 ∧ p4)) ∨ p4) ∧ p2) ∨ p3) ∨ True) ∧ (p4 ∧ False))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174365565486729837864653558800 : (((p5 ∨ ((p5 ∨ (p1 → p3)) ∧ (True ∧ (p4 ∨ p3)))) → (p3 ∧ (p5 ∨ False))) → (p3 → (((p3 ∨ p2) ∧ (p3 → p2)) → (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (p5 ∨ ((p5 ∨ (p1 → p3)) ∧ (True ∧ (p4 ∨ p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h13
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h20 : (p5 ∨ ((p5 ∨ (p1 → p3)) ∧ (True ∧ (p4 ∨ p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h22 := h1 h20
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122295482828001034265914571577 : (((False ∨ (((p4 ∧ p1) ∧ ((p3 → False) ∧ p3)) ∧ (p1 ∧ ((p1 ∨ True) ∧ (((p2 ∧ p2) ∨ p3) → True))))) ∧ (p4 ∨ p3)) → (p1 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h7.left
    let h15 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h31.left
    let h35 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h29.left
    let h37 := h29.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h41 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h42 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h43 := h34 h42
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h45 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h44
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h46 := h34 h45
        -- False on the left can always be used.
        apply False.elim h46
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h48 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h49 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h35
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h50 := h34 h49
        -- False on the left can always be used.
        apply False.elim h50
      case inr h51 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h52 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h51
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h53 := h34 h52
        -- False on the left can always be used.
        apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50006678758954476354613029058 : ((((p3 → (((p5 → p4) → (p1 ∧ p1)) ∨ False)) ∨ (p3 ∨ (p1 ∨ (((p5 → p3) ∨ True) → p4)))) ∧ ((False ∨ p5) ∨ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157315898367086314044561248167 : (((p3 ∧ ((((True ∨ (p4 ∨ p4)) → ((p5 ∧ (p5 ∨ p3)) ∨ p3)) ∨ (True ∨ p5)) → True)) → False) ∨ (p5 → ((p2 → p2) ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113552190773112536218395163678 : (((((p4 ∧ p1) → p5) → (True ∧ ((p5 ∧ ((((p2 → True) ∨ (p4 → p2)) → p5) ∨ p3)) ∨ (False → p4)))) ∨ (p1 ∧ p5)) ∨ (p4 ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642731041361970142698891336002 : ((((p1 ∧ ((p3 → p5) ∨ ((((((p2 ∧ p5) ∨ p4) ∨ ((p5 → False) → (p4 ∧ (p2 ∨ (True ∧ p4))))) ∨ False) ∨ p3) → p4))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607681398776575469025926212960 : (((((p5 ∧ (p5 ∨ (True ∧ (((p2 ∧ p2) ∨ p1) ∨ (p4 ∧ (((p4 ∧ p5) ∧ p5) ∨ (p2 → ((p4 ∨ p3) ∧ p4)))))))) ∧ p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194245282066867269978478159429 : ((p4 → ((False → p1) ∨ ((p2 → (p5 ∧ p2)) → p4))) → (((((False ∨ (p4 → p2)) ∧ True) ∧ (p3 → p1)) ∧ p4) → ((p2 ∧ p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734923020100814013157501829723 : ((((p2 ∨ p4) ∧ (((True ∨ True) ∧ (p5 ∨ ((((p5 → (True ∧ (((p1 → True) ∧ False) ∨ (p1 ∨ False)))) → p1) ∨ p3) ∧ p5))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152016495710170602629677961479 : ((((((p2 → p1) → ((p4 ∧ p2) → p1)) ∨ False) ∧ p5) ∧ ((p1 ∨ (p4 ∧ ((False → p1) ∨ False))) → p3)) → (((True ∧ p3) → p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730419925897049182874017397935 : ((((True ∧ (p5 → p2)) → ((True ∧ (((p4 ∨ p3) → p4) ∨ (((p4 ∨ True) → p2) ∨ ((p4 ∨ p4) ∧ (True ∨ False))))) ∨ (p4 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180265163458503405807769866360 : (((p5 ∨ (p1 ∨ (p1 ∨ ((((False → p2) ∧ p3) → p2) → p2)))) → p3) → (p2 → (p3 → (p3 → ((p5 ∧ (p2 → False)) ∨ (p3 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147052683472762538028773904919 : (((((((True ∨ p2) ∧ ((p5 → True) → p4)) ∨ p4) ∧ p2) ∨ (((p1 ∧ (p1 → p4)) ∧ p1) → p5)) ∧ p4) ∨ (((p5 ∧ True) ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259431539038281302776429326239 : ((False → p4) → ((((((p5 ∧ (False → True)) → p5) → ((p5 → False) ∨ (True ∧ p3))) ∧ (((p2 → (p4 ∧ True)) → False) ∧ p3)) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677698258695962026482138461968 : (((((((True → (p4 ∨ p5)) → p1) ∧ (p5 ∧ (p4 ∨ (False ∨ (p5 ∧ (p4 ∨ (p3 ∧ p4))))))) → False) ∨ (False → ((p4 → p1) ∧ False))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116068713851515177604926031958 : ((((p3 ∨ p4) ∧ False) ∧ (((True → p5) → p1) ∨ (((((False ∨ ((False → p3) ∨ True)) → (p1 ∨ p1)) ∧ p3) ∨ False) ∧ True))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330738593905989208645929283062 : (True → (p1 → (((((((p3 ∨ (True ∧ p5)) ∧ ((p1 ∨ True) → p1)) → (p5 ∧ p3)) ∨ True) ∨ p4) ∧ p2) ∨ ((False ∧ p1) → (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190418261219627975624133591008 : (((p1 ∨ (((p2 ∧ p3) ∧ p1) ∨ (p3 ∧ p4))) ∨ p2) ∨ ((p1 → (False ∧ ((False ∨ (p3 → (p3 ∧ True))) → (p1 ∧ p1)))) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85985224666798200637776076122 : ((((((p2 → p2) → False) ∨ p4) ∧ (p1 ∨ (p3 ∧ True))) ∧ (p5 ∧ (((True → (True → (((p4 ∧ p4) → p3) ∨ p3))) → p5) ∨ p2))) → p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h11 : (p2 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : (p2 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h24 : (p2 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h26 := h6 h24
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h28 : (p2 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h29
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h30 := h6 h28
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h3.left
      let h34 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h3.left
      let h41 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h43 =>
        -- One of the premise coincides with the conclusion.
        exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64254172292130518669806938124 : ((False ∨ (p3 ∨ (p4 ∧ ((p4 → (((p4 → p5) → p1) ∧ (True ∨ (p3 ∧ ((p5 ∧ p2) ∧ (p3 ∨ ((p3 ∨ p4) ∧ True))))))) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114531809984836961375453489352 : (((p4 ∨ ((((p2 ∨ (p4 ∧ p3)) → p4) ∨ p5) ∨ (p4 ∧ (p4 ∧ (p2 ∨ (p4 ∧ p1)))))) → (p1 → (p5 → (True → p4)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152492896439629186697096020712 : ((((True ∧ p2) → p4) ∨ (((p1 ∨ p4) ∧ p2) ∨ (p5 ∨ ((p3 ∨ (p5 ∧ p3)) ∨ ((p4 → p4) ∨ p5))))) → (((p2 → p5) → p1) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158504724775784742062591857040 : (((True ∨ p1) → (p2 ∨ (p5 → (((p1 ∧ False) ∨ (p2 ∨ (p1 ∨ (p4 ∨ (p4 ∧ False))))) ∧ False)))) ∨ (p3 → (((p5 ∧ p1) ∧ False) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55287286925327150970302367425 : (((p1 ∧ (p4 ∧ ((False ∧ True) ∧ p4))) ∨ ((p3 ∨ (((((False → False) → False) → ((p4 ∧ True) ∨ p5)) ∨ (p5 ∨ p3)) → True)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622130377137527814628498938904 : ((((p2 ∧ (((p4 ∧ p4) ∧ (((True ∨ p4) ∧ p5) ∧ p5)) ∨ (True → (p3 → (True ∨ (p1 ∧ (((p3 ∨ True) → p5) ∧ p2))))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688625878000197138352033811443 : ((((p4 ∨ (False ∨ (p4 ∨ (((p2 ∧ p3) ∧ p3) → ((p2 ∨ (p1 ∧ p3)) ∧ p2))))) ∧ ((p4 → (p2 ∨ p4)) ∧ ((p4 ∧ p4) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357079315323967431434505545785 : (p5 → (((False → p5) ∨ p4) → ((((p2 ∨ ((p3 → False) ∧ p4)) ∧ (p3 ∨ p1)) ∨ p4) → (True ∧ ((p1 → p4) ∨ (p5 ∧ (p1 → p1))))))) := by
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
        cases h2
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h22 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h23 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h24 := h19 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h26 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h27 := h19 h26
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h30
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h32
          -- One of the premise coincides with the conclusion.
          exact h31
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h35
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h36 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h37
      -- One of the premise coincides with the conclusion.
      exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54473092667997773390544628096 : ((((p4 ∧ ((p4 ∨ p5) ∨ p1)) ∧ (False ∧ False)) ∨ (((False → p4) ∨ (p2 ∧ (p1 ∧ (p4 ∧ (((p2 ∨ p4) ∨ p3) ∨ p1))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_817371841137654722628392549061 : (((((p4 ∨ (((p2 ∨ ((p4 ∨ (p2 → ((p4 ∨ p3) ∨ (False ∨ (p1 → (p1 → (p3 ∧ False))))))) ∧ p4)) ∨ True) ∨ p4)) → False) ∧ p3) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 ∨ (((p2 ∨ ((p4 ∨ (p2 → ((p4 ∨ p3) ∨ (False ∨ (p1 → (p1 → (p3 ∧ False))))))) ∧ p4)) ∨ True) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164752655444100085237763210085 : ((((True ∧ ((p2 ∨ p5) → (((p2 ∧ (p5 ∧ p1)) ∧ p1) ∨ p2))) → (False ∧ False)) ∨ p4) ∨ ((p2 ∨ True) ∨ (False ∨ (p3 ∨ (p1 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799596935984447131698415267691 : (((p1 → (p5 ∨ (((False ∧ ((p3 ∧ (((p5 ∨ (p1 → ((p4 ∨ p2) → False))) ∨ ((p5 ∨ False) ∧ p1)) ∨ p3)) ∨ p3)) ∨ True) ∧ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774512592460426668782243951172 : (((False ∨ (((((p1 ∧ p5) → (((p3 ∧ (p1 → p3)) ∧ True) ∧ p5)) → p4) ∨ True) ∨ ((p2 ∨ (((p4 → p4) ∧ p1) ∧ p1)) ∧ False))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_124283121773323925873493009451 : ((((p5 → ((False → p3) ∧ (p5 → p4))) ∧ p3) ∧ (True ∧ (p3 ∧ (False ∨ ((True → p1) → ((p4 ∧ True) ∧ (False ∨ p3))))))) → (p1 → p4)) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (True → p1) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640848361365102990456022229375 : (((((p3 → p3) ∧ ((p3 ∧ (p3 ∧ (((p5 → (False → ((False ∨ (p4 ∧ p2)) → True))) → p3) → (p1 ∨ p2)))) → (True → p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677260160173042396512969084671 : (((((((p5 ∨ False) → (False ∨ (p5 ∨ False))) → ((p1 ∧ (p3 ∧ (p3 ∧ (False → True)))) → True)) ∧ p1) ∨ (((p1 ∨ False) ∨ p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305164310884683759672568878788 : (p1 ∨ (((((p3 ∨ ((p2 ∨ p4) ∧ (p2 ∧ ((p4 ∨ False) ∧ False)))) ∧ p3) ∧ ((True ∨ p4) → p1)) → p4) ∨ (((False ∧ p1) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111779811431918563323948555223 : (((((p4 → ((p5 ∨ p4) → (p5 ∧ (((p4 → ((p2 ∧ p5) ∨ (p4 ∧ False))) → p1) ∨ False)))) ∨ False) ∨ (p5 → p2)) ∨ p4) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718595515163915103340383592422 : (((((False ∧ p5) ∧ (p2 → p5)) ∨ (True → ((((p3 ∨ ((True → p2) ∨ (((p3 ∨ p3) ∨ p4) ∨ (True → True)))) ∨ True) ∨ p2) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56240767073580257272861977780 : (((p5 ∨ (p5 → (False ∨ p1))) ∨ ((p4 → (p5 ∨ (p2 → (p1 → p2)))) → ((True ∨ p5) → (p5 → (p2 ∧ ((True → p5) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254706300994240336107929841790 : ((p3 ∧ p3) → (((p2 → (p2 → (((p5 → p4) ∧ False) ∧ (((False ∨ p5) ∨ (p4 → (True ∧ (p2 → p5)))) ∧ p1)))) ∧ True) ∨ (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_941217734614115764451927661212 : (((((p4 ∨ p5) → ((p2 ∨ True) → True)) → ((p2 → ((False ∧ p4) ∨ ((p2 → p4) ∧ (((False ∧ (True → p1)) ∨ p4) ∧ p5)))) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p5) → ((p2 ∨ True) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345374419192876487205572078015 : (p3 → (((((p4 ∧ False) ∧ p3) ∧ ((((p4 ∨ p2) → p4) → (p1 → (p4 ∨ ((p5 ∨ True) ∨ (True ∧ (True ∧ p4)))))) ∧ p1)) ∨ p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810386620829104487624055442038 : (((p5 → ((p4 ∨ ((p2 → (p5 ∧ ((p1 ∨ p3) ∨ p2))) → p4)) → (((False ∧ True) ∨ (((True ∧ (p2 → True)) → p3) ∨ p5)) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349513698375586403224054986264 : (p4 → ((((((p5 ∨ ((((p1 ∧ (p2 ∨ p4)) ∨ p2) ∧ False) ∧ (p4 ∧ False))) ∨ (False ∧ (p5 → (p4 ∨ p2)))) ∨ True) ∨ p3) ∧ p4) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55094722433303487396061007856 : (((p3 → ((p4 ∧ (p2 → p5)) ∨ p1)) ∧ ((False ∨ False) ∨ (p3 → ((p4 ∨ (p4 ∨ ((True → p4) ∨ p2))) ∧ ((p4 ∧ False) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46992186469950015135740093895 : ((((((p3 → ((p4 → ((p4 → p3) ∧ False)) → p2)) → p5) → (((False → p2) ∧ (p4 ∨ p4)) ∨ (False ∨ p5))) → p4) ∨ (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149417319067807200977987811816 : ((True ∧ ((True ∧ (p4 → (p2 → p4))) ∧ ((p4 ∨ p3) → ((((p2 ∨ (p3 ∨ False)) ∧ p5) ∨ p1) ∨ False)))) ∨ (p4 ∨ (True ∨ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116079954437402800835368052312 : ((((False ∧ p3) ∨ True) ∧ ((((p1 → ((True → False) ∨ (p3 → p2))) ∧ (p4 ∨ (True → ((p2 ∨ False) ∨ False)))) ∨ False) ∨ True)) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_167890014555340360335011458695 : (((p5 → ((p1 ∨ p2) ∧ (True ∧ ((p2 ∨ p3) ∨ p4)))) → (p1 ∧ ((p1 ∨ p3) → False))) → ((False ∧ ((p3 → p2) ∧ (True → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_847900186553491219921949939259 : ((((True ∧ (p2 ∧ ((False ∨ (p3 ∨ (p1 ∨ True))) → ((((p1 ∨ (p1 ∨ p4)) → False) ∨ (p2 → (p2 ∨ (False ∧ p5)))) ∧ False)))) ∨ False) → p4) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ (p3 ∨ (p1 ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594998291631525166131019788564 : ((((((True → (p2 ∨ (p5 → (p3 ∧ (p3 ∧ (True ∨ p3)))))) ∧ (p1 ∨ p4)) ∨ (p1 ∨ (p2 → ((False ∨ (p5 → False)) ∧ p2)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736546628756525066643702537915 : ((((p1 → p3) ∧ ((p1 ∨ ((((False ∨ (p5 ∧ False)) ∧ p5) ∧ ((False → p1) ∨ ((p4 ∧ p3) → p2))) → p3)) → ((p5 ∨ p3) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177728201507577625984036898192 : ((((p2 ∨ (p2 → (p2 → p5))) ∨ (p1 ∧ (False → (p4 → p3)))) ∧ p5) ∨ (((p2 ∨ (p2 ∨ False)) ∨ ((p4 ∨ False) → True)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136461249310783105132667325913 : (((p3 → ((False ∧ p3) ∨ True)) → ((((p5 ∨ (((True → p3) → p1) ∨ False)) ∨ ((True → p4) → p2)) ∨ False) → p2)) ∨ (True ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299242620205185040256443288868 : (False ∨ ((((p1 ∧ p2) ∨ (p5 ∧ ((p2 ∨ p5) → (p4 → (((p4 ∧ ((p1 → p5) ∧ p4)) ∨ p4) → p1))))) ∨ (p3 → (p2 ∨ True))) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184741700909845602426199905137 : ((((p5 ∨ (p3 ∧ p1)) ∨ p1) ∧ ((False → (False ∧ p1)) → p5)) ∨ (False ∨ (((p5 → p3) → ((p4 ∧ True) ∧ (p1 ∨ p2))) → (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



