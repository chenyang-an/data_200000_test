variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159028821504017178233884945595 : ((p4 ∨ (True ∧ ((((((p2 → (p3 → False)) → False) ∨ p5) → ((p2 → False) → p1)) ∧ p3) ∧ False))) ∨ (p1 → ((p2 → True) ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184099647773600611526296984833 : ((((p1 ∧ p1) ∧ (((False ∨ p1) → p2) → (p5 ∨ p5))) ∨ True) ∨ ((p3 ∧ ((p3 ∧ (True ∨ p5)) ∨ ((p1 → (p2 ∧ p5)) ∧ p1))) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115582938424603323556976224650 : ((((p2 → (p1 ∨ False)) ∨ (p2 ∨ False)) ∧ (((False ∨ p1) ∨ True) ∧ (p3 ∧ ((p2 ∨ (False ∨ p5)) ∨ (False → (True → p1)))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190529127880696805261068804622 : ((((p4 ∧ ((p2 ∨ p1) ∧ (p4 ∨ p4))) → p5) → p1) ∨ ((((p5 ∧ (((p3 ∧ p5) → p4) ∨ False)) ∧ p2) ∨ (p3 → p5)) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133988381128333956147827206352 : ((((((True → (p2 ∨ (p4 → p2))) ∨ ((True ∨ ((p1 ∨ (True → False)) → p1)) ∧ p1)) → (p1 ∨ False)) ∧ True) ∨ False) ∨ (False → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150902288244589810083239923615 : (((((p4 ∨ p3) ∨ p4) → (((p4 ∧ (False ∨ ((p1 ∨ False) ∨ True))) ∨ (p5 ∧ (True ∧ p3))) ∧ False)) ∨ p5) → (((p2 → p4) ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_232096036525889334190854793172 : (((p5 ∨ True) → False) → ((((p1 ∧ (False → (((p5 → p2) → True) ∨ p4))) ∧ (((p4 ∧ p5) → p5) ∨ (p4 ∨ (p4 → p3)))) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166322740447272718202935284092 : ((p5 ∧ ((((p4 → (p3 → p1)) ∧ p2) ∧ (p5 ∧ False)) ∧ (((p4 → False) ∨ False) → p4))) ∨ (((p2 ∧ (p1 ∨ p5)) ∨ p3) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666524513405572661929086805388 : ((((((p1 ∨ False) ∨ (((p2 → ((p4 ∧ (p5 → p2)) → p4)) → True) ∧ p1)) ∨ (p1 ∨ (p1 ∨ (p1 ∧ p4)))) ∧ ((p3 ∧ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634597412350797112694582000273 : (((((p5 ∧ ((False ∨ True) ∧ (p2 → ((True ∨ ((((p4 ∨ p5) → False) → p2) ∧ p3)) ∨ (p1 ∨ False))))) ∧ (False ∨ (p4 → False))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391714112226500900294432298408 : ((((((p2 → (p5 → False)) ∨ p1) ∨ (((p2 → ((p1 ∨ (p1 ∨ p2)) ∧ (False ∨ p1))) ∧ p2) ∨ (((False ∧ p1) ∧ p5) ∨ p1))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_134949273743867900181388575090 : (((((((p3 → p3) → (p3 ∧ (p4 → p4))) ∨ (p2 ∧ (p5 ∧ p1))) ∨ p1) ∨ (p3 ∨ (p2 ∨ True))) ∧ (True ∨ False)) ∨ (p2 ∨ (False ∧ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261365837219909998934737231046 : ((p5 → False) → (p3 → ((p4 → ((True ∨ ((((p3 → p3) ∧ p4) ∧ p5) ∨ ((p4 ∧ (p5 ∨ False)) ∧ p5))) → (p2 ∨ p1))) ∨ (p3 ∨ p4)))) := by
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
theorem thm_5_vars_44509803336046624623196108750 : ((((((p2 ∨ p4) ∧ ((True → (p3 ∨ True)) ∧ p4)) ∨ p1) ∨ ((p1 ∨ True) → (((p2 ∧ p4) ∨ (False → p1)) ∧ (p5 ∨ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51885958910756745407397145143 : (((((True → (p3 → (((False ∨ (p3 ∧ (p4 ∨ p1))) ∧ False) ∧ True))) → p3) → p3) ∨ (p1 → ((((False → p2) ∧ False) ∧ p3) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41620051680953058345423912328 : (((((((p5 ∨ True) → (True ∨ True)) ∨ False) ∨ p5) → ((((False ∨ (True ∧ True)) ∧ (False ∧ (True ∨ p2))) ∧ p1) ∨ (p4 → True))) ∨ p1) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684897545521018513959707303557 : ((((False ∧ ((p2 ∧ True) ∨ (True → (((p2 ∨ (p4 ∨ ((p3 → p1) → p3))) ∧ p2) ∨ p2)))) ∨ (((p2 ∨ (True ∧ p2)) ∨ True) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213531306412373588207158787075 : ((((True ∧ False) ∧ p2) ∨ p1) ∨ ((((p5 ∨ ((False → (p2 ∧ (p4 → p4))) ∨ p1)) ∧ ((p5 ∨ ((p1 ∨ True) ∨ p1)) ∨ p5)) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((False → (p2 ∧ (p4 → p4))) ∨ p1)) ∧ ((p5 ∨ ((p1 ∨ True) ∨ p1)) ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217597000558372141694492670522 : ((((True → p5) ∨ False) → p3) → (p1 → ((((((p1 ∨ p2) → ((p3 → p5) → p4)) ∧ True) → ((p4 ∨ p2) → p2)) ∨ True) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322279603363320941339495210766 : (p5 ∨ ((((((False ∧ (p4 ∧ ((False ∨ ((False ∧ p1) → p4)) ∨ True))) ∨ ((((True ∧ p2) ∨ False) → p1) ∧ p5)) → False) ∨ False) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706086129116914886541914609078 : (((((p5 ∨ p5) ∨ ((False ∨ (False ∨ p1)) ∨ p3)) ∧ (((False ∨ ((p3 ∨ p2) ∨ ((p5 → p2) ∨ ((p4 ∧ p2) ∧ p2)))) ∧ True) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177905680471234871295095085546 : ((((p5 → (((p4 ∨ p4) ∨ p1) → (p4 ∧ False))) ∨ (p2 → p1)) ∨ True) ∨ ((True ∧ (p5 → (((p2 ∨ p2) ∨ p4) ∨ (p5 → True)))) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791477538227065932498863793116 : (((True → ((p4 ∧ ((((((True ∨ p1) ∨ True) → True) ∧ (p2 ∨ p5)) → (False ∨ (p5 ∧ ((p3 → True) → False)))) → (p4 → False))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_65767675032571797603283577962 : ((p4 ∨ ((p5 ∨ ((p2 ∧ (p5 ∧ ((False ∨ (((p5 ∧ p1) ∨ False) ∧ p1)) ∨ p3))) ∧ p3)) ∧ (p4 → ((p3 ∧ p4) → (p4 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670038579870724941562456424829 : (((((((p4 ∧ p4) ∨ p4) → (p5 ∧ (p1 ∨ p1))) ∨ (p2 → ((p3 ∧ p1) ∨ (p4 ∧ (False ∧ (p1 → p3)))))) ∨ ((p2 → p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114837998764033764216979784334 : (((((p3 ∧ ((p3 ∧ (p4 ∨ ((p3 ∧ p5) → p1))) → p2)) ∨ p4) ∧ False) ∨ (p1 ∧ (((p1 ∨ p2) ∧ (p2 ∨ False)) → p2))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164805394627679931348894778730 : (((((True ∧ p5) → True) → ((p1 ∨ p5) ∧ ((p3 ∧ p2) → ((p2 ∧ True) → True)))) ∨ p3) ∨ ((p4 ∧ ((True → (p5 ∨ p5)) ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350253014611969911240835013936 : (p4 → ((p1 ∧ ((((p5 ∧ ((((p1 ∨ p4) ∧ True) ∧ ((p4 ∧ p3) → ((p3 ∧ p5) ∨ (p1 ∨ p1)))) → p2)) → p3) → p3) ∧ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114216445108497333215907027826 : ((((p4 ∨ p4) ∧ (p1 ∧ (p4 ∧ ((p1 ∨ (p5 ∧ p1)) ∧ ((p5 → p3) ∧ ((p4 ∧ p5) ∨ p1)))))) → (p2 ∨ (False ∨ p5))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136843576387695901525623590927 : (((p2 ∧ p5) ∨ ((((p4 ∨ False) ∨ (p1 ∧ (p5 → (p5 ∧ p1)))) ∨ (((p3 ∧ False) → p5) ∨ p2)) → (True ∧ p4))) ∨ ((True → False) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657132804974849349539017851562 : ((((((p3 ∨ p2) → p5) ∨ ((((p1 ∨ p3) ∨ ((((True ∨ False) ∨ p1) ∨ p1) → (True → True))) → (p2 ∧ False)) ∧ False)) ∨ (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246517711795697648228890297291 : ((p5 ∧ p1) ∨ ((p1 ∧ (((True → p4) ∨ (p5 → p2)) ∨ (p1 ∧ ((True → False) ∨ False)))) ∨ (((p4 ∨ False) ∨ True) ∧ ((p4 → p4) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324122436647971129191537231402 : (p5 ∨ ((p3 ∨ ((True ∧ ((p4 ∨ ((False ∧ False) ∨ p4)) ∨ False)) ∨ p2)) → (p5 → (((False ∨ p5) → (False ∧ p5)) ∨ ((p3 ∨ p5) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- False on the left can always be used.
            apply False.elim h12
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312992159138107830390986687921 : (p3 ∨ (((((True ∧ p5) → (False ∧ ((((p1 ∨ p5) ∨ (((p2 ∨ p4) ∧ (True ∧ True)) ∨ p4)) ∧ p4) ∧ (p1 ∨ p2)))) ∧ p5) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257142840315168432843023224821 : ((p2 ∨ p1) → (((True ∨ p3) ∧ (((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) → ((p4 ∧ p5) ∧ p2))) → (p4 ∧ (False ∨ (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : ((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : ((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : ((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h23 : ((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h24 := h4 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- One of the premise coincides with the conclusion.
      exact h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h2.left
  let h28 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
      have h32 : ((True ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h28, we can now drive its conclusion.
      let h33 := h28 h32
      -- We need to get the right conjuct of h33 based on <expert-advice>.
      let h34 := h33.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h34
  case inr h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h35
    case inr h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138000454383420121634568584336 : ((p5 ∨ (True → (((p1 ∨ ((((p1 ∨ False) ∧ ((True → p4) → ((p4 ∨ p4) ∧ p5))) → False) → True)) → p1) ∧ p2))) ∨ (p3 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721711748657603812617246304441 : ((((False ∨ (p4 ∨ (p5 ∧ p3))) → (((p1 → ((False ∨ p2) ∧ (((p5 ∨ (p1 → True)) ∧ p4) → (p3 ∨ True)))) ∨ p5) → (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40405000599354859000925472339 : ((((((((((p3 ∨ (p3 ∨ p3)) ∨ p3) ∨ ((p5 → p3) ∨ True)) → p1) ∨ (p5 ∨ False)) ∨ p1) → ((False → p4) → p1)) ∨ False) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347726199212525991289400732953 : (p3 → ((True ∨ (True ∨ p1)) ∧ ((((((p1 → p3) ∧ p3) → (True ∨ (p2 → False))) → p5) ∨ p5) → ((p3 → False) ∨ ((False → p5) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176069792398884187130107854206 : (((((p2 ∧ (False ∨ (p5 ∧ False))) ∧ p4) ∧ ((p5 ∧ p4) → p3)) → p3) ∧ (((p4 ∨ ((False ∧ p4) ∧ ((p1 → p1) → p4))) ∧ p4) ∨ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51560884239566631520040899680 : (((False ∨ ((((p4 ∨ True) ∧ ((True → (p2 ∨ p5)) ∧ ((p3 ∧ p4) ∨ p4))) ∨ p1) ∧ p5)) → (((p2 ∧ p5) ∨ (p4 ∨ p1)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767724134604247977335056038665 : (((p5 ∧ ((p4 → ((p1 ∨ p5) ∨ ((True → False) ∧ (((True ∨ (True ∨ (p3 ∧ (True ∧ ((p3 ∨ False) ∧ False))))) ∨ p4) ∨ p5)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215939760599191676123783605290 : ((p3 ∨ (p3 → (p2 ∧ p4))) ∨ (((((p4 ∧ p1) → (p1 → ((p2 ∧ p3) ∧ False))) → p3) ∨ p4) → (((p5 ∨ p1) ∨ True) ∧ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337578336236967945275435850169 : (p1 → (((((p2 ∨ ((True → p4) ∨ p3)) ∨ p5) ∧ ((p3 ∧ (True ∧ (False ∧ p4))) ∨ p5)) → (True ∧ p4)) → (p4 ∨ ((p5 → True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633227739558482774622680086225 : (((((True → (p2 → ((p4 ∨ ((p4 ∧ False) ∧ ((p5 ∨ True) ∨ (False → ((p3 → (True ∨ p3)) ∨ False))))) ∧ p2))) ∧ (p2 → p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204105879888145468637920999910 : (((((p4 ∨ p2) ∧ p1) ∧ p3) ∧ p2) ∨ (((p1 ∨ ((p2 ∨ p5) ∨ ((((p5 ∨ (p3 ∨ p4)) ∧ p1) ∨ p5) ∧ (p4 ∧ p4)))) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_65071327919858046874260027022 : ((p2 ∨ (p4 ∧ (True → ((True → (((p4 → (False → (p2 ∧ (True ∧ (p4 ∧ (p2 ∧ (False ∧ p2))))))) ∧ p2) → False)) ∨ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655311708172772344201417852110 : (((((p1 ∨ (True → (p4 ∨ (p3 ∨ (False ∧ (((p4 ∧ (p4 ∨ (p5 → False))) → p5) ∨ (False ∧ False))))))) ∧ (True ∨ p4)) ∨ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214199523575729766378302052453 : ((((True → True) → p3) → p5) ∨ (((((((p2 → p4) ∨ ((p4 ∨ (p3 ∨ p5)) → ((True → False) ∧ p2))) ∨ True) ∧ p1) ∧ True) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_339139080500504843936757904932 : (p1 → (p1 ∧ (((((p2 → (p3 ∨ ((p5 ∨ p3) ∨ p2))) ∧ p3) ∨ False) ∧ True) ∨ ((p1 ∧ ((((True → p5) ∨ p4) ∧ p5) ∨ p1)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146978780343994125642817939692 : (((((((True ∧ (p3 → True)) ∨ p3) ∨ p3) ∧ ((p1 ∧ (p2 ∨ (p1 ∧ p2))) → (p3 ∨ p4))) → p1) ∧ False) ∨ (((p5 → True) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190677216506461283788304231063 : (((p3 → ((True ∨ (p4 ∨ (p3 → p1))) ∨ p5)) → p4) ∨ (((False → (True ∨ (True ∨ ((p3 ∧ p2) → p4)))) ∨ (p5 → True)) ∨ (p3 ∧ p2))) := by
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
theorem thm_5_vars_153622848026312158327644252281 : ((p1 → ((False ∧ ((False ∨ p5) → (((True ∨ p1) ∧ True) → ((False → p1) → (p2 ∧ (p4 → p3)))))) → p1)) → (p2 ∨ ((p3 ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158129582288720742131665426347 : ((((p4 ∨ (p4 ∧ p5)) ∧ True) ∨ (p5 ∨ ((False ∨ (False ∨ (p3 ∧ ((p5 ∧ p4) → p5)))) → p2))) ∨ ((p5 ∨ p5) ∨ (p4 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_616465888749253535917050435253 : (((((((p4 → p1) → p2) ∨ (p1 ∧ ((p1 → True) ∨ (True → p4)))) → ((((p5 → (False ∨ (p1 → p1))) ∨ p1) ∧ p4) ∨ False)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_192412445770848761279783526889 : (((((False ∧ (p2 ∨ p4)) → (p1 → p3)) ∨ False) ∨ p4) → (((((p2 ∨ p3) → p1) ∧ (p5 ∧ p4)) ∧ (True → ((p2 ∧ p3) ∨ p2))) → p1)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (p2 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : (p2 ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h20 := h5 h19
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h24 := h4 h23
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h28 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h29 := h5 h28
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h31 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h32 := h5 h31
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49127376992551881212283022880 : (((((p2 ∨ (True → (False ∧ (p3 ∨ (p4 → (p4 → p1)))))) → p3) ∨ ((p2 ∨ (p4 → (p5 ∨ p1))) → p5)) ∨ (p2 ∧ (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257031879900138019042812417648 : ((p2 ∨ True) → ((p3 → (True ∧ (True ∧ p5))) → (p5 ∨ (p4 → (p2 ∨ (p5 ∨ (((p3 ∧ p3) → (True ∧ ((p3 ∧ p3) → False))) ∨ p4))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149465973405217982580603112461 : ((False ∧ ((p3 ∨ (p2 ∧ p2)) ∧ ((p4 → (((p1 ∧ False) ∧ (p5 ∧ False)) ∨ True)) ∨ (p4 → (p5 ∧ p1))))) ∨ (False → (p3 ∨ (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148377689761482338247658435651 : ((((((p2 ∧ (True ∨ (p4 → (p2 ∧ p4)))) ∧ False) ∨ p3) ∨ (p5 ∧ p1)) ∨ (p1 → ((True ∧ p5) → p5))) ∨ ((True → p1) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164873107323746352725859921913 : (((True → ((((True ∨ (p2 → p1)) ∧ (p4 ∨ (False ∨ (p3 → False)))) → p1) ∨ p3)) ∨ True) ∨ (False ∧ (p3 ∧ ((p1 ∧ p2) ∨ (p4 ∨ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263291554188714459844458039744 : (True ∧ ((True → (p3 ∨ (((((p3 → p5) → (False → (p2 ∧ p4))) ∧ (True ∧ (p3 ∨ ((p5 ∨ True) → p2)))) ∨ p4) → p1))) → (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134113280398595681011259008434 : ((((p3 ∧ (((True ∨ (p5 ∧ (True ∨ (True ∨ True)))) ∨ ((False → p4) → p1)) → (p2 → p5))) ∧ (True ∧ p2)) ∨ p3) ∨ (p1 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229454820483369045823913230926 : ((p1 → (p5 → p2)) ∨ ((True ∧ (((p2 ∧ (((p3 ∧ ((True ∧ (p3 → p2)) ∧ (p4 ∨ p2))) → False) ∧ (p3 ∨ p2))) ∧ p2) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660492123442866163397524645916 : ((((((((True ∧ p5) → (((p1 → p2) ∨ (False ∨ True)) → ((p4 ∨ ((False ∧ p4) ∨ p4)) ∧ p4))) → p5) ∨ p2) → False) → (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111516079162791118032291864993 : (((p5 → (((p1 ∧ ((True ∨ (True ∧ (p3 ∨ (p3 → (p4 → False))))) ∨ True)) ∧ True) ∨ (True → (p1 ∧ (p3 ∧ p2))))) ∧ True) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310207926850574815257548637938 : (p2 ∨ (((p4 → ((((p1 ∧ True) ∧ False) ∧ p4) → (p1 ∧ p4))) → p4) ∨ ((False → (p4 → (False → (p5 ∧ (p2 → (False ∧ True)))))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65561129561708999535699294827 : ((p3 ∨ (p2 → (((p4 ∧ (p3 → ((p4 ∨ (p2 → (((p4 ∨ False) → False) → p4))) → p4))) ∧ False) ∨ (True ∨ (p2 ∨ (p3 ∨ p5)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197545019535907766081908235218 : ((((p2 ∨ (p5 ∧ p2)) ∨ False) ∨ (p5 ∧ p1)) ∨ ((((p4 ∧ (p4 ∨ p2)) ∧ p1) ∧ p4) ∨ ((((p5 ∧ True) ∧ p4) ∨ (p4 → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300396290291155157253164711381 : (False ∨ (((False ∨ False) ∨ ((p4 ∨ ((((True → p5) ∧ p1) ∧ p2) ∧ p4)) ∨ (p2 → (True ∨ ((True ∧ False) → p4))))) ∨ (p3 ∧ (p5 → p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310040452221007985068801886216 : (p2 ∨ ((p4 ∧ (p5 → (((p4 → False) ∨ p1) ∨ (((p1 ∧ False) ∨ (False ∧ p3)) ∧ p3)))) ∨ (((p1 ∨ True) ∨ (p4 ∧ (p4 ∧ False))) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353411788556715191594422508125 : (p4 → (p1 ∨ (((((p3 ∨ (((p5 ∨ ((False ∧ p4) ∨ p3)) ∧ p4) ∧ (p4 → False))) ∨ p3) → p1) ∨ (p3 ∨ ((True ∧ p2) ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927269371571980785752142719666 : (((((((True ∨ (p1 ∨ (p2 → p2))) → p1) → p3) ∧ p1) ∧ ((p5 → ((True ∧ (((p1 ∨ p1) → p1) → p5)) → False)) ∨ (p1 ∧ p3))) → p3) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∨ (p1 ∨ (p2 → p2))) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354779755865032504876802353057 : (p5 → ((((((p2 ∧ True) → p4) → (p3 ∨ p4)) ∨ p1) ∧ ((p4 → ((p4 → p3) ∨ (p4 ∨ ((False ∧ True) ∧ (p2 → False))))) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168804430060962193395408904269 : ((p2 ∨ ((((((True ∨ (p2 ∧ p3)) ∨ (p5 → p4)) → p5) ∧ p2) ∧ p3) → (p1 ∨ p1))) → (((p3 ∨ (False → (False ∨ p2))) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ (False → (False ∨ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∨ (False → (False ∨ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786227212490549130557403554330 : (((p4 ∨ (((p3 → (((p1 ∧ ((p1 → (((p1 ∨ True) → p5) ∧ True)) ∧ p5)) ∧ p1) ∨ p4)) ∨ False) ∧ ((p3 ∧ (p4 → p5)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185316718228688171833008977942 : ((p3 ∧ (((False ∨ p4) ∧ (p4 ∧ (p4 ∧ p2))) ∨ (p3 ∧ True))) ∨ (True → (p5 ∨ ((False → ((False → ((p2 → p2) ∧ p5)) ∨ p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776917896209094318135923033428 : (((p1 ∨ ((p2 → ((((p5 ∧ p5) ∨ (((((p1 ∧ ((p1 ∨ p4) ∧ p4)) ∧ p2) ∨ p1) ∨ p4) ∧ True)) ∧ (p3 → p1)) → p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218059265967728551839811892909 : (((p3 ∨ p5) ∧ (True ∨ p1)) → ((((p2 ∨ p3) ∨ (False ∧ (False → (True → p5)))) ∨ (((p5 ∨ p3) → p3) → (p3 ∧ (False → p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (p5 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p5 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686453046984368307261264358670 : ((((((p4 → p2) → p3) ∧ (((True → p5) ∧ (p4 ∨ ((p2 ∨ (p4 → p4)) ∨ False))) ∧ p4)) → ((p2 ∨ p4) ∨ (False ∧ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84693703108011610238284806716 : ((((((((False → p3) ∧ p5) ∧ True) → (p3 ∧ (p5 → True))) ∧ True) → p1) ∧ ((((p2 ∨ (p4 ∨ True)) → (p4 ∨ p3)) ∨ p2) ∧ p3)) → p1) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((((False → p3) ∧ p5) ∧ True) → (p3 ∧ (p5 → True))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (((((False → p3) ∧ p5) ∧ True) → (p3 ∧ (p5 → True))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h16
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147481770479363453841818298041 : (((p3 ∧ (((True ∧ p5) ∧ (p4 → p1)) ∨ ((p4 ∧ ((p2 ∨ ((False ∧ True) ∨ p4)) ∧ p5)) ∧ p3))) ∨ p5) ∨ (((p5 ∧ True) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215550045397692779171099088817 : ((p5 ∧ ((p3 ∧ p5) ∧ p4)) ∨ (p3 ∨ (p3 → ((p5 → p1) → ((p1 ∨ p2) ∨ (p5 → (True ∨ (False → (False → ((p3 → p5) ∧ p2)))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53329814656172715987560695804 : (((((((p2 ∨ (False ∧ False)) ∧ p4) ∨ (p1 ∧ p4)) ∧ p1) ∧ p3) → (((p3 ∨ (p2 → ((False ∨ p3) ∧ True))) → (p4 ∧ p2)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38655346872225862081160250209 : (((((True ∧ p2) → (p5 ∧ ((p4 ∨ p4) → p5))) → (((True → ((p4 ∧ (p4 ∧ p2)) ∨ (p3 → p5))) ∧ (p2 ∨ p3)) ∨ True)) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317107978283929805995737649480 : (p3 ∨ (p5 → (((((p2 ∧ p1) ∨ ((((p4 ∨ ((p4 → p1) ∨ p3)) → p1) ∨ p2) ∨ (p5 → p5))) ∨ p3) ∨ (p3 ∨ p1)) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
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
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693791281940514220290036436871 : ((((((((p1 ∨ p4) ∨ False) ∨ ((p2 ∧ (p4 ∧ p2)) → p1)) → p5) → p4) ∨ (p1 → (((p1 → p2) ∨ p5) ∧ (p2 ∧ (p1 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52970172997418611116529021101 : (((((True ∨ (True → ((p3 → False) ∨ p5))) → (p5 → p3)) → p2) ∧ (p3 ∧ (((p5 ∨ (p2 ∨ p5)) → True) → (p5 ∧ (p5 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152878247588926398808917656302 : ((True ∧ (((((p3 ∧ (((p1 ∧ p1) ∧ p4) → (p3 ∧ p3))) → p5) ∨ False) → (True → False)) ∨ (p4 ∨ True))) → (((p2 ∨ p4) ∨ p5) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116307496130024666033462620599 : (((p2 → (p4 ∨ False)) ∨ ((((((p4 → p2) ∨ p3) ∨ (((p1 ∨ p2) ∧ ((p3 ∧ p1) → True)) ∨ p2)) ∧ p3) ∧ p1) ∧ p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323981171046909757701725198297 : (p5 ∨ (((p3 ∧ (True → ((p2 ∧ True) → (((p5 ∨ p1) ∨ p5) → p1)))) ∧ True) ∨ ((p2 → (p4 ∨ ((p5 ∨ p3) ∨ (p3 → False)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42084453438280673488094467826 : ((((p3 → p2) ∨ ((((((True ∧ p4) ∨ p1) ∨ p3) ∨ (p4 ∧ (p2 → False))) ∧ (p5 ∨ p1)) ∧ ((False → (True ∧ p4)) → p5))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799949247178967371038042428218 : (((p2 → ((((((True ∨ p4) ∧ p2) → (p3 ∧ (p4 → (p3 → p2)))) ∧ ((p5 ∧ (p4 → p1)) → (p4 ∧ (p5 ∧ False)))) ∨ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179389916287997217074217894196 : ((p3 ∨ (((((p1 → p3) ∨ p1) ∨ (p1 ∧ p4)) ∨ True) ∨ (True ∧ True))) ∨ ((p5 ∨ p3) ∨ (((((False ∧ False) → True) ∧ False) ∨ p2) ∨ p2))) := by
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
theorem thm_5_vars_53403292966332180309731166965 : ((((False ∧ ((p4 ∨ p1) → (p2 → (p5 ∧ p5)))) ∨ (p2 ∨ p1)) → (((True ∧ p5) → (False ∧ ((False ∨ (p5 ∨ p2)) ∧ p2))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219572187524273127050212166137 : ((True → ((p2 ∧ p4) → p1)) → (((p4 → p1) → ((True → (False ∨ False)) ∧ ((p1 ∨ ((p4 ∧ True) → p5)) ∧ p5))) ∨ (True → (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69037195398964126418626104850 : ((p5 → ((((False ∧ (p3 ∨ p4)) → (((p2 → (p4 → p3)) ∧ p1) → (p4 ∨ (p3 ∨ (False → p4))))) → ((p4 → p4) → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215544480075429157768468065231 : ((p4 ∧ (p4 → (p1 ∧ p3))) ∨ ((True → (p3 ∧ ((((p3 ∧ p5) ∧ False) ∧ (((False ∧ False) ∨ (p1 → p4)) ∧ False)) ∧ (p5 ∧ p3)))) → False)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199768266188208615613463897525 : (((p2 → ((False ∧ (p3 ∨ p1)) → p5)) → False) → (((((p1 ∨ (p4 → ((p3 ∧ p2) → (False ∧ p4)))) ∨ p3) ∨ p5) → p3) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((False ∧ (p3 ∨ p1)) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669427704473759611165326192967 : (((((((p4 ∧ p1) ∧ p4) ∧ (p2 → ((((p1 → True) → p1) ∧ (True → True)) → (p3 ∨ p1)))) ∨ (p1 ∧ p3)) ∨ ((p3 ∨ True) ∨ p3)) ∨ p2) ∧ True) := by
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



