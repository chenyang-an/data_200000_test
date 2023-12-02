variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149885841279054800047215368509 : ((p2 ∨ ((p2 → ((p1 ∨ True) → p1)) → (p4 ∧ ((p1 → p4) ∨ ((p3 ∧ ((p4 → p3) ∧ p2)) ∨ p1))))) ∨ ((p1 → (p5 → True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226020697905561822315520729407 : (((p4 ∧ p3) ∨ p4) ∨ (((p4 ∧ p2) ∨ (False ∨ ((p3 → True) → (True ∧ ((p4 ∨ p4) ∨ ((p3 → False) → ((False ∨ p2) → p2))))))) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114098314443439328293499983338 : (((p1 ∧ ((p3 → (p4 ∨ ((((True ∧ False) → (p5 ∨ p1)) ∨ False) ∨ ((p3 ∧ p5) ∨ p5)))) → False)) ∨ (False → (p2 → p1))) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172391817387030456744485210807 : ((((False ∨ (p5 → p3)) → (p2 ∨ p4)) → (((p4 ∧ (p1 → False)) ∧ True) ∧ True)) ∨ ((p5 ∨ ((p3 ∧ (p4 → (False ∧ p3))) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690717721574532200421373586995 : ((((((((p5 ∧ (p3 → p5)) → p4) ∧ ((p4 ∨ p4) ∧ (p5 ∧ False))) ∧ p2) → True) → (True ∧ (p5 → ((p4 ∨ (p1 ∨ p3)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304006922229363389376230233706 : (p1 ∨ (((p4 ∨ p5) → (((True → p2) ∨ (p5 ∧ (p1 ∧ ((True ∧ (((((p1 ∧ p3) → p1) ∧ False) → p3) → p4)) ∨ p3)))) ∨ True)) ∨ p5)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346591877759026303463488421290 : (p3 → ((((False ∨ ((p5 ∧ p1) → p3)) ∧ ((p2 ∧ (((p5 ∧ p2) ∧ False) → (p1 ∧ (False ∨ p3)))) ∧ p2)) ∨ p4) ∨ (p5 ∨ (False ∨ p3)))) := by
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
theorem thm_5_vars_256394030451500469644726257291 : ((False ∨ p3) → ((((p2 ∧ (((p3 → False) ∧ (True ∧ p1)) → (False → p5))) → ((p3 ∧ ((p1 ∧ p5) ∨ p1)) ∨ (p4 ∧ p5))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64856996302521500910299909029 : ((p2 ∨ (((p1 → p3) → (((((p4 ∧ p3) → p3) → (((True → p4) ∧ False) ∧ (False ∧ p3))) ∨ (p4 ∨ p4)) ∧ p4)) ∧ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121969528861840038946826682905 : (((False ∨ (p5 ∨ ((p2 → (False ∨ ((((True ∨ p4) ∨ p4) → p4) ∧ (p2 ∨ p3)))) ∨ (((p3 ∨ p5) → p1) ∨ True)))) → False) → (p2 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (p5 ∨ ((p2 → (False ∨ ((((True ∨ p4) ∨ p4) → p4) ∧ (p2 ∨ p3)))) ∨ (((p3 ∨ p5) → p1) ∨ True)))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306143430045535128911999163763 : (p1 ∨ (((p5 ∧ True) ∧ False) ∨ ((((p3 ∨ (p5 ∨ p4)) ∨ True) → ((p3 → p2) → (p3 ∨ True))) ∨ (((p2 ∧ p3) ∧ (p3 → p2)) ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115638925254757722322288864709 : (((((p5 ∨ p1) → (p3 ∧ False)) ∨ p2) ∨ ((False → p5) ∧ ((False ∨ (p4 ∨ p4)) ∧ ((p2 ∨ (p3 ∧ p5)) ∨ (True ∨ p5))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42151498010093637537636314615 : ((((False → p4) → (((p3 ∨ p5) → (((p3 ∧ p4) → ((True ∧ (((False ∧ (p3 ∨ p3)) ∧ p4) → True)) ∨ False)) → p3)) ∨ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197493508422801135905856633892 : (((p3 ∧ ((p5 ∨ p4) ∨ p4)) ∧ (p3 → True)) ∨ (((p4 ∨ (p3 ∨ True)) ∨ (p5 ∧ ((p4 → (p1 ∨ p3)) → (True → (True ∨ p1))))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251399816737949926713200424381 : ((p2 → p4) ∨ (p2 ∨ ((p2 ∨ ((p2 → ((p3 ∧ ((p2 → False) ∧ p4)) ∧ p3)) ∨ (False ∧ (p4 ∨ p3)))) ∨ ((p1 ∨ (False → p3)) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344875218487043177783395279789 : (p2 → (p5 → (p5 ∧ (p4 → ((p1 ∧ p4) ∨ ((((p2 ∧ ((p2 → ((False ∨ p5) ∨ (False → p4))) ∧ p3)) ∨ (False → p3)) → p1) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150706276059711940877325249234 : (((((((False → ((((p2 ∧ (p4 ∨ p2)) ∧ p4) ∨ (True → p5)) → False)) ∨ p1) → False) → p3) ∧ p1) ∨ p2) → (p5 ∨ (p2 ∨ (True ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65871445063175443508205386928 : ((p4 ∨ ((p1 ∨ p5) ∨ ((((((p4 ∨ p3) → p5) ∨ p2) → (((True ∨ p4) → (p4 → p5)) ∨ p3)) ∨ (False ∧ (p5 → p3))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27440001722738485346746823207 : (((p2 ∧ p4) → ((((p5 → (((p1 ∧ (False ∧ p3)) ∧ p2) → ((((p2 → p2) ∨ False) → p1) ∧ p4))) → False) ∨ True) ∨ (True ∧ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118205482393356267540186751220 : ((False ∨ (p5 → ((p3 ∨ (p2 → p3)) ∨ ((p5 ∨ False) → ((p1 → p2) ∨ (((True ∨ (p5 → (p4 ∨ False))) ∧ p1) ∨ True)))))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191537571467574518152790430180 : ((p1 ∧ ((True ∨ ((True → (p2 → True)) ∧ p5)) ∨ p5)) ∨ ((False ∨ p2) ∨ ((p3 ∨ (p5 ∧ p2)) → (((p5 ∧ (p1 ∨ p4)) ∧ p5) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80363153097926585894518450279 : ((((True → ((((p4 ∨ p1) → False) ∧ p2) ∧ (p2 ∨ ((p1 ∨ p5) → False)))) ∨ (((False → p1) → (p3 ∨ p1)) → True)) → (p3 ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((((p4 ∨ p1) → False) ∧ p2) ∧ (p2 ∨ ((p1 ∨ p5) → False)))) ∨ (((False → p1) → (p3 ∨ p1)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750270672481589444854229290842 : (((True ∧ (((True ∨ (p4 ∨ (p5 → True))) ∧ ((((False ∧ True) ∨ True) ∨ False) → (p4 ∧ ((p2 ∨ p4) ∧ (p4 ∧ p2))))) ∨ (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160915836230844894845789534006 : (((((True ∨ p5) ∧ True) → p5) → ((((p4 → False) ∨ ((p4 → (p3 ∧ p3)) ∧ p2)) → p2) ∧ p2)) → ((False ∨ p3) → (p2 ∨ (p3 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263813440787088401557048835254 : (True ∧ ((p5 ∨ ((p4 → (False ∧ p4)) → ((p1 → True) → (((p4 ∧ False) ∨ p1) ∧ p4)))) ∨ (((True ∨ (p2 → p4)) ∧ p3) → (p3 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328287182853411088617103510832 : (True → ((((((p4 ∨ (True → p4)) ∨ p5) ∨ (True ∧ (True → False))) ∧ (p2 → p5)) ∨ (False → (p2 ∨ p5))) ∨ ((p3 → True) ∨ (p1 → p2)))) := by
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
theorem thm_5_vars_172204222983769281611227705402 : ((((((p2 → (False → p1)) ∨ p2) ∨ p5) → (p4 ∧ p2)) → (p3 ∧ (p1 → p3))) ∨ (((p5 ∨ True) ∨ True) ∨ (p3 ∨ ((True → p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56656910053684817843495348806 : ((((p4 ∨ p1) ∧ p2) ∧ ((p3 ∨ ((p2 → p4) → p4)) ∧ ((((p5 → (p3 ∧ (False → p3))) ∧ False) → p3) ∧ (p4 ∧ (p3 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348870006145392469247860382273 : (p3 → (p2 ∨ ((p1 ∧ (p2 ∨ ((False ∨ (p5 → ((p3 ∧ (p3 → p4)) ∨ True))) ∨ False))) ∨ (p5 → (p1 ∨ (False → ((True ∨ p5) ∨ p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171596687371661281013203994012 : ((((False → ((False ∧ p5) ∧ ((True ∨ False) ∨ True))) → ((p3 ∨ p1) ∧ p1)) ∨ True) ∨ (p2 ∨ ((True → (p4 ∧ (p5 ∧ (True ∨ p4)))) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47559560735221290781635567488 : (((True → (p1 → ((((p4 ∧ p5) ∨ ((False ∧ (p2 → (p4 → False))) ∨ (True → p4))) ∨ (True → p2)) ∨ (True ∨ p5)))) ∨ (p2 ∧ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_193597404713395882264513182901 : (((p2 → p5) → ((p5 ∨ (p2 → (p4 ∨ p4))) → p5)) → (((p5 → False) ∧ ((p1 → (True ∨ (p4 ∧ True))) → p5)) → (p2 ∨ (p1 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → (True ∨ (p4 ∧ True))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255193218408365194622664480125 : ((p4 ∧ p4) → ((p3 ∧ (((p5 → ((p3 → ((p1 ∧ p2) ∨ p3)) ∨ ((p1 ∨ p5) ∨ False))) ∧ False) ∧ ((p2 → p4) ∧ False))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679551894499905598096582798666 : (((((((True → p1) ∨ (p3 ∧ True)) ∧ (((False → ((True → p1) ∨ (p2 ∧ True))) → p1) → p5)) ∧ p1) → (((p5 ∧ True) ∨ p4) → p5)) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h20 : ((False → ((True → p1) ∨ (p2 ∧ True))) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h22 := h18 h20
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h26 : ((False → ((True → p1) ∨ (p2 ∧ True))) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h28 := h18 h26
      -- One of the premise coincides with the conclusion.
      exact h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116972696244442497400813602308 : (((p4 ∧ p2) → ((False → (p1 ∧ p2)) → ((False → (((p2 ∨ (((p2 → False) → p1) ∧ p2)) → (p4 → p2)) ∨ True)) → p1))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259200190830839393587567307325 : ((False → False) → ((((((False ∨ (p3 ∨ (p5 → p5))) ∨ p2) ∧ ((p4 → ((p3 ∧ p5) → p2)) → (p1 ∨ p2))) → p5) ∧ p4) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225187669590884044976212977276 : (((p4 ∧ p2) ∧ p3) ∨ ((((p4 ∨ p2) ∨ p2) → (p1 → (((p3 ∨ ((p4 → (False ∨ ((p2 ∨ p1) ∧ p5))) → p3)) ∨ p1) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729547229898397595263582145744 : (((((p2 ∨ p5) ∨ p5) → (((((True → p4) → p2) ∨ (p3 ∧ False)) → (True ∨ False)) → (p4 ∨ (p2 ∨ (p1 ∨ (p5 ∨ (p5 → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192669594523999618173446862957 : ((((False ∧ ((p1 ∨ (p5 ∨ p3)) ∨ True)) → p3) → p5) → ((p5 ∨ False) ∨ ((False → (p1 ∨ p2)) ∧ ((p2 → p4) ∧ (p1 → (p4 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p1 ∨ (p5 ∨ p3)) ∨ True)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157203670874570515460550624283 : ((((p4 ∧ (((p1 → False) → ((p1 → (p5 ∧ p4)) ∨ p5)) ∨ (True ∨ p2))) ∨ (p1 → p3)) → p2) ∨ (True ∨ (((p4 ∨ p2) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352891126084045178298776293443 : (p4 → (True ∧ ((False ∧ (p5 ∧ ((p3 ∧ p4) ∧ False))) ∨ (True → ((p3 ∧ ((p1 ∨ (((p4 ∨ p2) ∧ False) → True)) ∨ (p2 → False))) ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603271979756427603840473010028 : ((((p2 ∨ ((p2 ∨ p5) ∨ ((True ∨ (False → (True ∧ ((p3 → True) → (p2 ∨ (p4 ∨ (p5 ∧ (False ∨ p1)))))))) → (p4 ∨ True)))) ∧ True) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84114962070939702665113863419 : ((((p2 → p2) ∧ (False ∨ (True → (p5 ∧ (((p2 → p5) ∨ (p5 ∧ True)) → False))))) ∧ (p5 ∧ ((((p5 → p2) ∨ p1) → p3) ∨ p5))) → p4) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : ((p2 → p5) ∨ (p5 ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h19 := h7 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : ((p2 → p5) ∨ (p5 ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h23 := h20 h21
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774458561135380700925935667792 : (((False ∨ ((p2 ∨ ((p5 ∧ (p5 ∨ p1)) → ((p4 ∨ False) ∨ ((False ∨ (p4 → p1)) → p5)))) ∨ (((p1 ∧ False) → p2) → (p1 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45120816003262100993723802089 : ((((p5 ∨ p5) → (p5 ∨ ((p4 → (p4 → (False → ((p1 → (((p3 ∧ (p5 ∧ (True ∧ True))) → True) ∨ p4)) → p3)))) → p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43225670265509257793652664244 : ((((False ∨ (((((p1 → False) → ((p4 ∨ p5) ∧ (p3 ∧ (((p4 ∧ p5) ∧ p5) ∨ p2)))) ∨ p2) → (False → True)) ∨ False)) ∧ p1) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681341824780816018195249736093 : ((((False ∨ (p2 ∧ ((True → ((p1 → True) ∨ (True → p3))) ∨ (((p1 → p4) ∨ (p3 ∧ p3)) ∧ p1)))) → ((p5 ∨ (True ∨ False)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149016531793461981992544826688 : ((((p2 ∨ p3) ∨ p5) ∨ (p4 ∧ ((((True ∧ p5) ∧ True) ∧ ((p4 → (p1 ∨ p5)) → (p1 ∨ p2))) ∨ True))) ∨ (True ∨ ((True ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255761759365086053679558708180 : ((True ∨ True) → ((p4 ∨ p1) ∨ ((p1 ∨ True) ∨ (p3 ∧ ((p3 ∧ (((p5 ∨ (p1 ∧ ((p5 ∨ p5) → p5))) ∨ p2) ∨ p3)) → (p3 ∧ p3)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218671234491160848966556241163 : ((True ∧ (p2 ∨ (True ∧ p3))) → ((((((p2 ∧ p4) ∨ (p3 ∧ (True ∨ (p3 → True)))) ∧ p3) ∧ ((p5 ∧ p3) ∧ p2)) ∧ p2) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50452569551081722722782841897 : (((p3 ∨ ((((p4 ∧ True) ∧ (((True → False) → (True ∨ False)) ∧ (p3 → p1))) ∨ False) ∧ (p4 → p3))) ∨ (((p2 ∧ p2) ∨ p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337051291522067975426967423964 : (p1 → ((((p2 ∨ (p2 ∨ (p4 ∨ p3))) → (p2 ∧ (((p5 → p5) ∨ (False ∧ (p2 ∧ (p3 → False)))) → (p4 ∨ p2)))) ∨ p4) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148305705207690234541680021602 : ((((p1 ∧ p1) ∨ (p4 → ((p1 ∨ p4) ∨ (p3 ∨ (p2 ∨ (False ∨ (p5 ∨ p3))))))) → ((p4 → p3) ∨ p1)) ∨ (((p3 ∨ True) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157651460883306389256081099378 : ((((p2 ∧ ((p2 ∧ False) ∨ (False → (True ∨ ((p5 ∧ p4) ∨ p2))))) ∧ p1) ∨ ((True → p3) ∨ False)) ∨ (True ∨ (p3 ∨ ((p2 ∨ p1) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113330880601189120188979268078 : ((((p4 ∧ p3) ∨ ((((p4 ∧ (True ∨ p1)) ∧ (False ∧ p3)) ∨ (p5 ∧ ((p5 ∨ p1) ∨ (p2 ∧ False)))) ∨ p1)) ∧ (False ∧ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50275027962799283168860924759 : ((((((p1 ∨ (True ∧ p4)) ∧ (((False ∨ p4) → p2) ∨ True)) → ((False ∨ p3) → p4)) ∨ (p3 → True)) ∨ ((p5 ∧ p2) ∨ (False ∧ p5))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40084194257675116988689330984 : ((((((p1 ∨ (((((p3 ∨ p2) → ((False → p3) → p3)) ∨ p4) ∨ p4) ∧ True)) ∨ ((p1 → (p2 ∨ True)) → p4)) → p4) ∧ True) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358232241490949175793499866865 : (p5 → (p4 ∨ ((p4 ∧ (p1 ∧ ((p5 → p3) ∧ (p3 ∧ (False → (((False ∧ p1) ∨ p3) ∧ ((p4 → p5) → p4))))))) ∨ (p1 ∨ (p2 ∨ p5))))) := by
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
theorem thm_5_vars_620165011635207916042609220196 : (((((p2 ∧ p1) ∨ (((p1 ∨ (True ∧ p1)) ∧ ((p5 ∨ p4) ∧ ((False → (p2 → (p5 → (p2 ∨ p3)))) → False))) → (p1 → p3))) ∨ p3) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (False → (p2 → (p5 → (p2 ∨ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h9
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : (False → (p2 → (p5 → (p2 ∨ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h19 := h7 h15
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h4.left
    let h24 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : (False → (p2 → (p5 → (p2 ∨ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- False on the left can always be used.
        apply False.elim h27
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h30 := h24 h26
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h32 : (False → (p2 → (p5 → (p2 ∨ p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h33
        -- Implications on the right can always be decomposed.
        intro h34
        -- Implications on the right can always be decomposed.
        intro h35
        -- False on the left can always be used.
        apply False.elim h33
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h36 := h24 h32
      -- False on the left can always be used.
      apply False.elim h36
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251314567676776947153818834859 : ((p2 → p3) ∨ ((p5 → (p4 → ((p3 ∧ p3) → (p5 ∧ (p3 ∧ (True → (p3 → (False ∨ p5)))))))) → (((p2 → p5) ∧ (True ∧ p3)) → p3))) := by
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
theorem thm_5_vars_169105210398683339277801045007 : ((p4 → ((False ∧ p1) ∧ (p2 ∧ (p5 ∧ (False ∧ ((((p2 ∨ p5) ∨ False) ∨ p2) ∧ False)))))) → (p4 ∨ (p5 ∨ (((p5 ∧ p2) ∧ True) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258086266922819844517671468786 : ((p4 ∨ p2) → (p3 → ((((True ∧ False) ∨ (p4 ∨ ((False ∧ p5) ∧ ((False → (p3 ∨ ((p2 ∧ p1) ∧ p4))) ∧ p3)))) ∨ (p4 ∨ p3)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123416206283535596152415564722 : ((((True → (((p1 → (p4 ∧ (p4 ∨ (p4 ∧ True)))) ∨ p2) → p3)) → (p4 → (p1 ∧ p1))) → (p1 → ((p2 ∨ p1) ∨ p3))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116606934588516970867816378020 : (((True → p1) ∧ (((True ∧ p5) ∨ ((p1 ∨ p5) → ((((p1 ∨ p4) → p3) ∨ (False → (p3 → p3))) ∧ True))) ∨ (p4 ∨ p2))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3938166784636597047692561299 : (False ∨ ((p2 ∨ p1) → ((((p4 ∧ (True ∨ p5)) ∨ p5) ∧ (((p4 ∨ p5) ∧ (p1 ∨ p2)) → p5)) ∨ ((True → p2) ∨ (p1 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4131730300323379500686911034 : (p3 ∨ (p5 ∨ ((p3 ∧ ((((((p5 → (False ∧ (p1 ∧ True))) → (False → p2)) ∧ p1) → (False ∨ (p4 ∧ p4))) ∧ False) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137234346593326703867556457345 : ((p1 ∧ (((p1 ∨ ((((p2 ∧ ((p4 ∧ p1) ∧ p1)) → p3) ∨ False) ∧ p5)) → ((p4 → True) → p1)) ∨ (True → p1))) ∨ (False → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306164137966424256011858302304 : (p1 ∨ (((p2 ∧ p2) → p1) ∨ (p1 ∨ ((p4 ∨ (((p3 → (p2 ∨ True)) → (p4 ∨ p1)) ∧ p3)) ∨ (False → (True → (p5 → (p3 ∧ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348214288184779402071615129612 : (p3 → ((p2 → p2) → ((((((p2 ∨ False) → p4) ∧ (False → p4)) → ((p1 ∨ (False ∨ ((p4 → (False ∨ p4)) → p4))) → p3)) → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p2 ∨ False) → p4) ∧ (False → p4)) → ((p1 ∨ (False ∨ ((p4 → (False ∨ p4)) → p4))) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h5.left
        let h14 := h5.right
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h15 := h3 h4
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49401736101126897367382122851 : ((((((p2 → ((p3 → p4) → p4)) ∧ True) ∨ ((p5 ∧ False) ∨ (True ∧ ((p4 → True) → (True ∨ p1))))) ∧ p4) → (False ∧ (True → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165516848984761005391583708371 : ((((((p5 → p2) → (p2 ∧ p1)) ∨ p5) → (p1 ∧ p4)) → (p1 ∧ (p1 ∧ (True → p1)))) ∨ ((False → p2) → (((True ∨ p4) ∧ p5) → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136337194182178270936951146199 : (((p1 ∧ (p4 ∨ (False ∧ p5))) ∧ (p5 ∧ (p1 ∧ (((((True → p2) ∨ p3) ∨ (p2 ∨ (p5 ∨ p2))) ∨ p1) ∨ p1)))) ∨ (False → (p2 ∧ p5))) := by
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
theorem thm_5_vars_45391828039626430578244041188 : (((p5 ∧ (((((p3 ∧ p3) → p3) ∧ (((p3 → True) ∧ (p3 → p2)) → True)) → (((p4 → p5) ∨ (p4 → False)) → p1)) → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225184784026955915193656262422 : (((p4 ∧ p2) ∧ True) ∨ (((p5 ∨ True) → (p4 → (p4 → p4))) → ((True ∧ ((((p5 ∧ True) → p3) ∧ (True → False)) ∧ p3)) → (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111215727832225850897088361017 : (((((p4 ∧ False) ∨ p5) → ((p5 ∧ (p1 ∨ ((p1 → True) ∧ p3))) → (((p3 ∧ p5) ∧ (p2 ∨ False)) ∨ (False ∨ p4)))) ∧ p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10139167646387894442964829074 : (((False ∨ (((False ∧ (p3 → (p4 ∨ ((p1 ∧ (p3 → ((p5 ∧ p4) ∨ (p5 ∨ True)))) → p5)))) ∧ p5) ∨ (p3 → (True ∨ True)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64613702846123959623778699102 : ((p1 ∨ (True ∧ (((p2 ∧ (((p2 ∨ ((p2 → p3) ∨ (p1 ∨ p2))) ∨ ((p5 → p3) ∨ True)) ∧ p2)) ∧ ((p3 ∧ p2) → p5)) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_215206510942033953064882170683 : ((True ∧ (True → (p1 ∨ p4))) ∨ (p1 → (((((False ∨ p1) → p2) → (p4 ∧ p1)) ∨ (False → (((p1 → p4) → p2) → True))) ∧ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700829168291071382661958286805 : (((((p2 ∨ (((p4 → p3) ∧ (True → p1)) → False)) ∧ p2) ∧ (((p4 ∧ (False ∨ ((p2 → p3) → (p5 ∧ p2)))) ∨ p4) ∨ (p5 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53142715304006923421723043885 : ((((p5 ∨ ((p1 ∧ (((False ∧ False) ∧ True) ∧ p1)) ∨ True)) ∧ p3) ∨ ((False → ((p3 ∧ ((p4 ∨ (p4 ∨ p1)) ∨ p2)) → p3)) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h1
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h1
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354410591526022741698082706933 : (p5 → (((True ∨ p4) ∧ ((((p5 → p1) ∧ (False ∧ p5)) ∨ ((p3 ∨ (p2 → (p4 ∧ True))) ∧ (p3 ∨ ((p2 ∧ p2) ∨ p3)))) ∨ True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670611038504655887082317679848 : (((((p5 → p4) ∨ (((True → (((False → p5) ∨ p1) ∧ p1)) ∧ p5) ∨ ((p5 → p1) ∨ (p2 ∧ (p5 ∧ True))))) ∨ (True ∧ (p3 ∨ True))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249989246276726926624956716447 : ((True → p2) ∨ (((True ∨ False) ∨ p5) → ((p5 → (p2 ∧ (((p5 ∧ ((p5 ∧ False) ∧ p3)) ∨ p2) ∧ (p3 ∧ False)))) ∨ ((True ∨ p4) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51175086496581225187220608273 : ((((((True ∨ ((((True ∧ (True → p1)) ∧ p1) ∨ p4) ∨ p2)) ∧ p5) ∧ p3) → (p4 → False)) ∨ ((((p2 ∨ p5) ∧ p3) → True) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310424321702918448859577044360 : (p2 ∨ (((p4 ∨ ((p3 ∧ p5) ∧ p5)) ∧ (p4 ∧ p5)) → (p1 ∨ (((True ∧ (p2 → p5)) → p2) → ((((False ∧ p3) → p4) → p4) ∧ p2))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (True ∧ (p2 → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h20
    -- One of the premise coincides with the conclusion.
    exact h17
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h21 : (True ∧ (p2 → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h23 := h19 h21
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115059200403352069556213234306 : ((((((False → (p3 ∨ p4)) ∧ p4) ∨ p3) ∧ (True → (p1 ∨ p4))) ∨ (((p4 ∧ p3) ∧ (p1 ∧ p3)) ∧ ((p2 ∨ p3) ∨ p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64816381468526509378346209420 : ((p2 ∨ (((p4 ∧ ((p1 ∨ p5) → (p3 → (p1 → ((p5 → (p3 ∨ ((True → (p1 → (p2 → p5))) ∨ p1))) → p2))))) ∨ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52527080460808652925737408066 : ((((((False ∧ ((p4 ∧ p1) ∧ p1)) ∧ (p1 → False)) ∧ (p1 → p5)) ∨ p4) ∨ (p2 → (p2 ∨ (((p4 → p5) → (p3 → p3)) → p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327068337659522598219239322064 : (True → ((((p5 ∨ p5) → (False ∧ False)) ∨ (((p3 ∨ False) → ((p4 → (p1 → ((True ∧ (p4 ∧ False)) ∧ (p3 ∨ False)))) ∨ True)) ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_112148375551508886738210386860 : (((p1 ∧ (p4 ∧ ((p1 → (p3 → True)) ∧ (((False ∧ p2) → ((p1 → ((p2 ∨ (p4 ∧ True)) ∨ False)) ∨ p1)) → p5)))) ∨ True) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58488239634309367076406489557 : (((p4 ∨ p1) ∧ (p4 ∧ ((False ∧ (((p1 ∧ (((p1 ∨ False) ∨ p3) ∨ p4)) ∧ p1) ∨ p1)) ∨ ((((p4 ∧ p1) ∧ p1) ∨ p2) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158789674913209317855906347312 : ((p5 ∧ ((True ∨ ((p1 ∨ ((p2 → True) ∧ (((p1 ∧ p5) ∨ True) → p4))) → True)) ∧ (p3 ∨ p2))) ∨ (((p4 ∧ (p1 ∨ True)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636161620595135533683911372036 : ((((((((p5 ∨ p3) → (True → ((p2 → p5) → (True ∧ p3)))) ∨ p2) → (False ∨ p1)) ∨ ((((True → p5) ∧ p3) → p4) ∧ p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117077408674132107989101992144 : (((False → True) → (((p2 → (p4 ∨ (p4 ∨ ((p5 ∧ p4) ∨ p3)))) ∧ (p1 ∨ (p4 ∧ (p1 → (p5 → (False ∧ p5)))))) ∨ True)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137780759514261282926337921090 : ((p2 ∨ (((p1 ∧ p1) ∨ (True → p3)) → (p4 ∧ (((False ∧ (p4 ∨ True)) ∧ ((True → False) ∧ (p1 ∨ p5))) ∨ False)))) ∨ (p1 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134742170838002261987559653811 : ((((p4 → p4) ∧ (((p4 → (p4 ∨ ((False ∧ ((p4 → (p2 ∧ p3)) ∨ p2)) ∧ False))) ∨ (p1 ∨ p2)) → p4)) → p5) ∨ (p5 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41988914857814505761767706955 : ((((p5 ∨ p2) ∧ ((False ∧ (((((False ∧ (p5 ∧ (p4 ∧ p2))) → (p3 ∨ p1)) ∨ False) ∨ p1) ∧ p5)) ∧ ((True → p2) ∧ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57673785217443099700456492381 : ((((p1 → False) ∨ True) → ((((False → (p1 ∨ True)) → (True → ((True ∧ p4) ∨ (True ∧ True)))) → p4) → (((p4 ∧ p3) → p1) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173081159893263126851267107830 : ((p1 ∨ ((((p2 → (p4 ∨ (p5 → (p2 → (True ∨ True))))) ∧ True) → p3) → p1)) ∨ ((False ∨ p1) → ((((p2 ∧ p3) ∨ False) ∨ True) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227734528574051736220396352534 : ((p1 ∧ (False ∨ p2)) ∨ ((False ∨ (p5 ∨ p5)) → (((((((p4 ∧ p2) → (p4 ∧ True)) ∧ p5) ∧ p5) → (p1 ∧ p1)) ∧ (p2 → p1)) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



