variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172383854521552232752326874979 : ((((False ∨ (True ∧ (p2 ∧ p5))) ∨ p3) → (p1 ∨ (((p4 → False) → p1) ∧ p5))) ∨ ((((p5 → p5) ∨ p2) ∧ True) ∨ (p4 ∧ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263900603844810521779259083679 : (True ∧ ((True ∧ (p5 ∧ (((p2 ∧ True) ∨ ((p4 ∧ p3) → True)) → (p1 ∨ p4)))) ∨ (((True ∧ (p1 → (p2 ∧ (p5 → False)))) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_207692592740402341602137601596 : ((((True → p4) → (False ∨ False)) → p5) → (((p4 → p3) ∨ (True ∧ ((True → p4) → (True ∨ p3)))) ∨ (((True ∨ True) ∧ p2) → (p5 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325703416313887144781105321689 : (p5 ∨ (p1 ∨ ((p2 ∧ (p1 → p4)) ∨ (((p4 ∨ (((p1 → True) → False) → (False ∧ p5))) ∨ (False ∨ (((p5 ∧ False) → p3) ∨ True))) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193210703814574840759349874782 : (((p4 ∨ (p1 → (False ∨ p2))) → (p3 → (p2 ∨ True))) → ((p2 → ((p4 → (p5 ∧ False)) → p5)) ∨ ((p5 → (p2 ∨ p5)) → (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203827071096289287643937756835 : ((False → ((p3 → (True ∨ False)) ∧ p4)) ∧ (p3 → ((((((((p1 ∧ p4) ∨ p5) → p3) ∧ p2) ∧ p2) → (True → p5)) → False) ∨ (False → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218634248870458142578031208390 : ((True ∧ ((False ∧ p3) ∨ p1)) → ((p1 ∧ (((p3 ∨ p1) → (p1 ∧ ((p4 → ((p2 ∧ p1) ∨ (p2 → False))) ∧ p2))) ∨ (p1 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167855334327557781937605759767 : (((p4 ∨ (((True ∧ p3) → (p2 ∨ p2)) ∧ (True ∨ False))) ∨ (((p2 ∨ p5) → p5) ∨ True)) → ((p4 ∨ p1) ∨ (False ∨ ((True → p4) ∨ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179239112211993500326868503867 : ((p5 ∧ ((p3 ∨ ((p3 ∨ (p5 → p2)) → (p1 ∨ (True → p3)))) ∨ p2)) ∨ ((True → ((p3 ∨ p3) → ((False ∧ p1) → p2))) ∨ (p1 → p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49916039012372725477233892587 : (((((p4 ∧ (((False → p1) → p2) ∨ (True ∨ ((p2 → p5) → p2)))) ∧ ((p2 → False) ∧ p4)) → False) ∧ ((p2 ∨ (p2 → p3)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203650497304055749106200628818 : ((p3 ∨ ((p2 ∧ (p2 → p5)) → p2)) ∧ ((((((p5 ∨ False) ∧ p2) ∨ p2) → p5) ∧ (p5 ∨ (p3 ∧ (((p5 → p2) ∧ p5) ∧ p3)))) ∨ True)) := by
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
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167589320193537235261546244248 : ((((False ∨ p3) → (False ∨ (((True → (True ∨ p4)) ∨ p2) ∨ (True ∨ p5)))) ∨ (p4 ∨ p3)) → ((p3 ∨ (((False → True) → False) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613873439976388617241476634115 : (((((((p4 ∨ (p5 ∨ p5)) ∨ (p1 → (True ∧ (False ∧ (((p1 ∨ (p3 ∧ p4)) ∧ p1) → True))))) ∨ p1) ∨ ((p2 ∨ p5) ∨ True)) ∨ p5) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_104700330071448281099486074347 : (((p2 → ((((p5 ∨ ((p4 ∧ p1) ∨ p5)) → False) ∨ p5) ∧ (False ∨ ((p4 ∧ ((True ∧ False) ∧ True)) ∧ False)))) ∨ (False ∨ True)) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_777491891500394022672875290520 : (((p1 ∨ (((p3 ∨ ((True ∨ False) → (p3 ∨ (((p5 ∨ p2) ∨ p3) ∨ p5)))) → p2) ∨ ((False ∧ (p5 → p5)) ∨ (p3 ∧ (p5 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657760291240357649195675141143 : ((((True ∧ ((True ∧ ((p3 → (False ∨ p1)) ∧ ((False → (p2 → (p2 ∧ p4))) ∧ p1))) ∧ (((p2 ∨ p4) ∨ p3) ∨ p4))) ∨ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62328980326348513569178757230 : ((p3 ∧ ((p2 ∧ ((True ∨ (p3 ∨ ((p3 ∨ True) ∧ p5))) → (((p3 → p2) ∧ (False ∨ ((p4 ∨ p4) → p2))) ∨ True))) → (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313160710153134229451518542250 : (p3 ∨ ((((p1 → (((p1 ∨ ((p5 ∨ False) ∨ False)) ∨ p1) ∨ p3)) → p1) → ((p5 ∧ (p3 ∧ p5)) ∨ (((p2 → p3) ∨ False) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70048990959984705212684626364 : (((((p2 ∨ (p3 ∧ (((True ∨ (False → ((p4 ∨ p3) → ((p2 ∧ p1) ∨ False)))) ∨ (p2 → p1)) → p5))) ∨ (True ∨ p4)) → False) ∧ p1) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (p3 ∧ (((True ∨ (False → ((p4 ∨ p3) → ((p2 ∧ p1) ∨ False)))) ∨ (p2 → p1)) → p5))) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351781455234296256811731901089 : (p4 → ((((((p2 ∨ p5) ∨ True) ∨ False) ∧ (p5 ∧ (p2 ∧ p1))) ∨ p4) ∧ (p5 ∨ (True ∧ ((p2 → p3) → (((p1 → p3) ∧ False) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149063108754726008643860256666 : ((((True → False) ∧ p1) → ((((p1 ∨ (p4 → p3)) ∨ (p1 ∨ p5)) → False) ∨ ((p1 ∧ (False → False)) ∨ p1))) ∨ (p2 ∧ (p4 ∧ (p3 ∨ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631926081919762960672938801422 : ((((((p1 ∨ ((p1 → True) ∨ p3)) ∨ ((True ∧ ((p3 ∧ (p4 → (p2 → False))) → (p1 → (False ∨ (p2 → p3))))) ∨ False)) → p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315834269464627576474251059219 : (p3 ∨ ((True → True) → (p1 → (p3 ∨ ((((p4 ∧ True) ∨ p5) ∧ p2) ∨ (((False ∧ p5) ∨ (True → (((True → p2) → p1) ∧ False))) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40605944649477835655142483550 : (((((((p1 → ((p3 ∨ (p3 ∧ (((p4 ∨ (True ∨ p3)) → p3) ∨ p5))) ∧ False)) ∧ (p3 ∨ False)) ∧ (p1 → True)) ∨ p3) → False) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241419039155906820315144458188 : ((False → p1) ∧ ((p5 ∧ (((p4 ∧ p4) ∨ (False ∧ (p4 ∧ p5))) ∧ p4)) ∨ (((False → (((p1 ∧ True) ∧ (p5 → p2)) ∧ p4)) ∨ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_244371861699079253585899482068 : ((False ∧ p1) ∨ ((((((p2 ∨ ((True ∨ (p2 ∧ (False ∨ p3))) ∧ False)) ∨ True) → p3) → p3) → ((p5 ∧ (p3 ∨ False)) ∨ (True ∧ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741666657063813500536722686852 : ((((True → False) ∨ ((False ∧ ((p1 → ((p2 ∧ p1) ∨ (p4 → p5))) → (False ∧ p5))) ∨ (((True → (p4 ∨ False)) → p5) → (p3 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55037771242191446898297984302 : (((p4 ∧ ((p5 ∧ True) ∧ (p1 → p2))) ∧ (p2 → (p5 ∧ ((p1 ∨ ((p2 ∧ (True → (p4 ∨ True))) → (p1 → p2))) ∨ (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151634727627204677843878792154 : ((((((p4 → (p1 ∧ (p3 ∨ ((p2 ∨ False) → (p4 ∧ p5))))) → True) ∨ p4) ∧ p4) ∧ ((p3 → p3) ∨ p3)) → ((p2 → p1) ∨ (p4 ∨ False))) := by
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
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147080827471404041298744507084 : ((((((p3 ∧ p2) → p3) → False) ∧ (((((p2 → p4) → p5) → (False → (True ∨ p1))) ∨ p3) ∨ True)) ∧ p1) ∨ ((False → p3) ∧ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301381413621139307357065009743 : (False ∨ (((p5 ∨ False) ∨ (p4 ∨ p1)) ∨ ((p3 → (p2 ∨ (((False → (p4 → (False → (p5 ∧ False)))) ∨ p4) ∧ p3))) ∨ (p1 ∨ (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731615835283199129154250130926 : ((((p1 → (p2 ∨ True)) → (((((p2 ∨ p3) → ((p1 ∧ True) → p4)) ∧ (False ∨ (p1 → (p4 ∧ ((False ∨ p1) ∨ p4))))) ∨ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716356789405826534934385044264 : (((((False ∨ p5) ∧ (p4 ∨ p1)) ∧ (((((((p1 → p1) → (True ∨ False)) ∨ p4) ∨ (p1 ∧ (p1 ∨ (True ∨ p3)))) → p5) ∨ p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39219237070752519352122416250 : (((True ∧ (((p3 ∧ p2) ∨ p2) ∨ ((((p2 ∨ (p1 ∨ p5)) → ((False → p4) ∧ ((p2 → (p1 ∨ True)) ∨ True))) → p2) ∧ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180683117652910362622506020117 : ((((p4 ∧ p2) → ((False ∨ p3) → p4)) → (False ∨ ((p4 → p3) ∧ p3))) → ((True → (False ∧ ((p1 ∨ p3) → (p4 ∨ (p2 → p2))))) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312400075415120013002482775863 : (p2 ∨ (p3 → (p1 → ((False ∧ (p5 ∧ (((p2 → True) ∨ p4) → (p5 ∨ p5)))) ∨ ((((p3 → p4) → (p5 → (p3 → p3))) → p1) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348724119521254636853696502514 : (p3 → (False ∨ ((True ∧ ((False ∨ ((((p3 ∨ True) → False) ∧ (((p1 ∧ (p3 → False)) ∨ p3) ∧ p1)) ∧ p3)) → (p5 ∨ (p1 ∧ False)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h17 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h18 := h7 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118737616197778220743705009774 : ((p5 ∨ (((True ∨ p3) → ((p1 ∧ (False → p3)) → (p4 ∧ p4))) ∨ (p5 ∨ (p5 → ((False ∨ False) ∨ ((False ∨ p1) ∨ p5)))))) ∨ (p5 ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118816003270630560469890229649 : ((True → ((p2 ∧ (p5 ∧ (((p2 ∧ ((p5 ∨ True) ∨ p1)) ∨ ((True → (((p5 ∨ False) ∧ p3) ∨ p2)) ∧ p3)) → p5))) ∨ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231894057506543266281374489211 : (((True ∨ p5) → False) → ((p1 ∧ p4) ∨ (((p4 ∨ p2) ∨ ((p2 ∧ (p1 ∧ (((((p1 ∧ p5) ∧ False) → p5) → p3) ∨ p2))) ∧ p3)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798061388363586388382482758834 : (((p1 → (((p3 ∨ ((p3 → p3) ∧ p4)) ∧ ((((p2 ∨ False) ∧ (p3 → p1)) ∨ p1) → ((True ∨ p4) → p2))) ∨ ((p4 ∨ True) ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778510641914268246674807257463 : (((p1 ∨ (p5 ∧ ((p1 → ((((False → p4) ∨ (p4 ∧ True)) → p3) ∧ False)) → ((p1 ∨ (p1 ∨ p5)) → (((False → p2) ∧ p1) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191282468750423134818337754606 : (((p4 ∨ True) ∧ ((False ∨ (p5 ∧ (False ∨ False))) ∨ True)) ∨ (((p5 → p5) → (p2 ∧ (p4 → p2))) ∨ (p4 → ((p4 → (p5 ∨ p4)) ∨ False)))) := by
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
theorem thm_5_vars_111146781186401058226039459119 : ((((((p4 → p5) ∨ (False → p2)) ∧ p4) ∨ (((p2 → (p2 → (False ∧ p1))) ∧ p1) ∨ (False → ((p5 ∧ True) ∧ p5)))) ∧ True) ∨ (p3 → p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51584353167471479906070930200 : (((True → (((p2 ∧ (p3 ∧ p1)) ∨ p3) ∧ ((((p1 ∧ p2) ∨ (p3 ∨ p1)) ∧ p1) → p4))) → ((p2 ∧ (True → (True ∧ p4))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160794851639788157603834310228 : ((((False ∨ (p2 ∧ p5)) ∨ (True ∨ p4)) ∨ (((p4 ∧ p5) ∨ p4) ∨ (((p4 → False) ∧ p2) → p5))) → ((p5 → (p3 ∨ p5)) ∨ (True → p2))) := by
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186813169581758273720268252486 : (((p4 ∨ ((p5 → False) → p3)) ∧ (p2 ∧ (True → (p4 ∨ p3)))) → (((p4 ∧ (p1 → (True ∧ p1))) ∧ ((p2 → p4) ∨ (True → True))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197824309434231454865800612043 : (((False ∧ (p1 ∧ p5)) ∨ ((False ∨ False) ∧ True)) ∨ (((p4 → (p1 ∧ p1)) ∧ (((p2 ∧ p3) ∨ p5) → ((p4 → p5) ∧ False))) → (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∧ p3) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746005662343691438425881502421 : ((((False ∨ p5) → ((True → p1) → ((p1 ∨ p4) → ((((p4 ∧ p5) ∧ (p3 ∨ (((True → (p5 ∧ p1)) ∧ False) ∧ p1))) ∧ False) ∨ p1)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179389930840143891199097390304 : ((p3 ∨ ((((p2 ∧ p4) ∨ ((p5 ∧ p2) → p4)) ∨ p2) ∨ (p2 → p2))) ∨ ((p5 ∧ (((p1 ∧ p5) ∧ (False → p1)) ∨ False)) ∧ (p1 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127791184610321077715168207122 : ((True → ((p5 ∧ (p4 ∧ (p4 ∧ False))) ∧ (((p4 → False) → ((True → p4) ∧ (False ∨ p5))) → (p3 ∧ (p1 ∨ (p4 ∨ p5)))))) → (p1 ∧ p3)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
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
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133752396997319254714766140032 : ((((True ∧ ((((p4 → p2) → False) → p2) → p3)) → ((False → p2) ∧ ((((p2 ∨ p2) → p5) ∧ p4) ∨ False))) ∧ p1) ∨ ((p1 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50195288234564418804944450230 : ((((p2 ∨ (((((p5 ∧ (p3 ∨ False)) ∨ p4) ∧ (p3 ∨ (p2 → p3))) ∧ p2) → (True ∧ True))) ∧ p2) ∨ (((p4 → p2) → p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149263567899633176412900348136 : (((p5 ∨ False) ∨ (p1 ∨ (((((False ∧ (p3 ∧ True)) ∧ (p4 ∧ True)) ∨ (p5 ∨ True)) ∧ True) ∧ (False → p5)))) ∨ (p1 → (p3 ∧ (p3 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39159521650663142166574941826 : ((((p3 ∨ p1) → (((p5 ∧ p4) ∨ ((((((p2 ∧ (p1 → False)) ∧ (p4 ∧ p2)) → False) ∨ p1) → (p1 ∨ p5)) ∨ p1)) → p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52606574686507757736872584346 : ((((p1 ∧ ((False ∨ p4) ∧ False)) ∧ ((p5 → (p5 → (p3 ∨ True))) ∨ p3)) ∨ (p5 ∨ (((p2 ∧ p4) ∨ ((p4 ∧ p5) → p4)) ∨ False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328145181928137811743726737272 : (True → ((False ∨ ((p4 ∨ True) → (((False ∨ (p5 ∧ ((p2 → p1) ∨ True))) → (p4 ∧ p1)) ∧ ((p4 ∧ p3) → p1)))) ∨ (False ∨ (False → True)))) := by
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
theorem thm_5_vars_37887482978731144774602058724 : (((((((False ∧ (p2 ∨ False)) → ((p1 ∨ ((False → True) ∧ p1)) → ((p5 → False) ∨ (p2 ∧ True)))) ∧ p4) → False) ∧ (p3 ∧ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124090966440387117473613422226 : (((((p1 ∧ p4) → (((False ∧ p2) → p5) ∧ False)) ∧ p4) ∧ (((p3 ∨ p1) → (p3 ∧ True)) ∧ ((p5 → True) → (p1 ∧ True)))) → (p1 ∧ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h13.left
  let h17 := h13.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h20 := h17 h18
  -- We need to get the left conjuct of h20 based on <expert-advice>.
  let h21 := h20.left
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h22 : (p1 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h21
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h23 := h14 h22
  -- We need to get the right conjuct of h23 based on <expert-advice>.
  let h24 := h23.right
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164816490566984369325728085278 : ((((p4 ∧ p1) ∨ ((p1 ∧ (p1 ∨ (p1 ∧ ((p5 → p4) ∨ p5)))) → (p1 ∧ False))) ∨ True) ∨ (False ∨ ((False ∨ (True → (p5 → True))) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45527177108006509920726198946 : (((p1 ∨ ((False ∧ p1) ∨ (p3 ∨ ((((((((p4 ∨ p2) ∧ p5) ∨ p4) ∨ p5) ∧ (True → p3)) ∨ False) ∧ (p4 ∨ p2)) ∨ p4)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943250864447648009740435956028 : (((((p2 → True) → (p4 → False)) ∧ ((((True → (((True ∧ p3) ∧ (True ∧ ((True ∧ p4) ∨ (p4 ∨ p1)))) ∧ p1)) ∧ p4) ∧ p1) ∧ True)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h10
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57973854189869325971687569285 : (((p3 → (p4 ∨ p4)) → ((p1 ∧ p4) → (((False ∧ (p2 ∧ (p3 ∧ ((p5 ∨ True) ∧ (p4 ∧ p4))))) ∧ (p3 → p3)) ∨ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161611970181972468896215462362 : ((False ∨ (((((p1 ∨ ((p3 ∨ p3) ∧ False)) → False) ∨ ((p3 → p2) → p4)) ∨ p1) ∨ (p1 ∧ False))) → ((((p3 ∨ True) → False) ∨ p4) ∨ True)) := by
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
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262415898156122703530533683569 : (True ∧ ((p1 ∧ (((False ∨ p4) → ((p2 → (p1 → ((False ∨ False) ∨ (False → p3)))) → (((p4 ∧ (False ∨ False)) ∨ p5) ∨ p2))) ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244161688829304302004349287139 : ((True ∧ p4) ∨ ((p2 ∧ True) ∨ ((((p5 ∧ True) → p5) → (((((p4 → False) ∧ p4) ∧ p4) → (True → (p2 ∧ (p3 ∨ p4)))) ∧ False)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ True) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171339912520698069660530627210 : ((((((p4 → p3) ∧ (p5 ∨ ((False ∧ p4) ∨ (p3 ∧ p3)))) → p3) → False) ∧ False) ∨ ((p1 ∧ p3) ∨ ((False → p2) ∨ (p2 ∧ (p5 ∨ True))))) := by
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
theorem thm_5_vars_113293877623468102451604505238 : (((((p5 → (False ∧ ((p2 ∧ True) ∨ p2))) ∨ p4) ∨ ((True → (p5 ∧ (((p3 ∧ p4) ∨ p4) ∨ p5))) ∨ True)) ∧ (p5 → p5)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337946298744940577100839730650 : (p1 → (((((((p1 ∧ p3) ∨ p3) → p4) ∨ True) ∧ False) ∧ (p4 → p3)) ∨ (((True ∧ p5) ∨ (True ∧ (p1 → p3))) ∨ ((False → False) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192263728906209805821768474328 : ((((p4 ∨ (p1 → p5)) ∨ ((False ∧ p3) → False)) ∧ p4) → (((p1 ∨ p3) → (((p5 → (True ∧ p3)) ∨ True) ∨ (False → False))) ∨ (p2 ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
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
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152214416559375531157587868926 : ((((p4 → (p3 ∧ p1)) ∧ (False → p5)) ∧ ((((((p1 → p5) ∧ p1) ∧ True) ∨ True) ∧ (p3 ∨ p3)) ∨ p3)) → (p4 → (p4 → (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h20
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h25 := h6 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h28 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h29 := h6 h28
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4642817425837222792458447383 : (p5 → ((((p1 ∨ (p2 ∨ p1)) ∧ (p3 → (p5 ∧ (p2 ∧ (False ∨ (p5 ∧ (False → (p2 → p5)))))))) ∨ (p2 ∧ p2)) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327144093613467023722947165481 : (True → ((p2 ∧ ((((p3 ∨ p1) ∨ ((p1 ∨ True) → p3)) ∧ ((((((p3 ∨ p5) ∨ False) → p4) → (p2 ∨ p1)) ∧ p1) ∨ p2)) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61284069370933706123923442927 : ((False ∧ (p4 ∨ (p4 ∧ ((p3 → p5) ∧ (p2 ∨ (((((False ∧ p3) → p3) → (p4 ∧ (p5 ∨ (True ∧ False)))) ∧ (p4 ∧ p5)) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57427825565645791753961654288 : (((p3 ∨ (False ∧ p1)) ∨ (p3 ∨ (p2 ∨ (((((p1 ∧ ((p5 → (False → (False → True))) ∨ False)) ∨ True) ∨ p1) ∨ (False ∧ p3)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199933232652234733819828705828 : ((((p3 → False) → (p5 ∧ p5)) ∨ (p4 → p2)) → (False ∨ (((False ∧ False) ∨ p1) → ((p5 ∧ (p2 ∨ (((True ∨ p2) → p2) ∨ p4))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256945176263915703248608015589 : ((p1 ∨ p5) → ((p2 ∨ ((p1 ∧ (p3 ∨ (p5 → (p5 → p1)))) → ((p2 ∧ True) ∧ ((p5 → True) → ((p2 ∨ False) ∧ (p3 ∨ p1)))))) ∨ True)) := by
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
theorem thm_5_vars_111562052134136851765036877083 : ((((((False ∨ (p2 ∧ p5)) ∨ (p1 ∧ (p3 ∧ True))) ∨ (p5 ∧ ((p2 → True) → ((True ∧ p5) ∧ (p3 ∨ p3))))) ∧ p3) ∨ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351718430214804163401866734509 : (p4 → ((((False ∨ (p1 ∧ ((p3 → False) ∧ p1))) ∧ (p2 → (False ∧ p5))) ∧ p4) ∨ (p4 ∨ ((False ∧ (p2 ∨ (p5 → (True ∧ p5)))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234667571484332831843715680095 : ((p4 → (p1 ∧ p2)) → ((((p2 → (((p2 ∨ p3) → (((p3 ∨ (False ∧ (p5 ∨ p1))) ∧ p2) → p4)) ∨ p2)) ∨ p1) ∨ True) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40052082075452095835405143680 : ((((((p1 → ((p2 ∨ ((p4 ∨ (p3 → (((p2 ∧ (p2 ∨ p4)) ∧ p1) → p3))) → (p1 → p3))) → p3)) ∨ p3) ∨ True) ∧ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313160830322547831639666046627 : (p3 ∨ ((((p5 → (p3 ∧ (p5 ∧ ((False → p3) ∧ p5)))) ∧ (p1 → p4)) → (((True ∨ (p1 ∧ False)) → (p1 ∨ p2)) ∨ (p3 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41791522249203839183613274180 : (((((p1 → p3) ∧ (False ∨ True)) → ((((p3 ∨ (((True ∨ (p2 → p5)) ∨ p3) ∧ True)) ∧ (p4 → (p1 ∧ p5))) ∧ p4) → p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861575793214916663694822337018 : ((((((p5 ∨ ((p3 ∧ ((p4 → (p4 → (True → p1))) ∨ (p4 → True))) ∨ ((True → p3) ∧ True))) → False) → ((p2 → p5) ∨ True)) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ ((p3 ∧ ((p4 → (p4 → (True → p1))) ∨ (p4 → True))) ∨ ((True → p3) ∧ True))) → False) → ((p2 → p5) ∨ True)) := by
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
theorem thm_5_vars_175197514611054336593988967038 : ((False ∨ ((p4 ∨ (p2 → ((p2 → p4) ∧ (True ∨ (False ∧ True))))) ∨ (p5 ∧ p1))) → ((p2 ∨ p3) ∨ ((p3 → p1) → (p1 → (p1 ∧ True))))) := by
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
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138311812216266588784587011309 : ((p3 → ((p2 ∧ (p2 ∨ p1)) ∨ (((p2 ∧ (((True ∧ p5) ∨ True) → (False ∨ (False → p1)))) ∧ p3) ∧ (True → p2)))) ∨ ((p2 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57462179183037485141403595477 : (((True → (p2 ∧ p5)) ∨ ((False ∨ ((True → p4) ∧ ((((p1 ∧ (p1 ∨ p3)) → p3) → (p2 ∨ ((p5 → p1) ∧ p4))) → p3))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2490866457119450455534802153 : ((((False ∨ p1) → (p2 → False)) ∨ (p3 ∨ (p1 ∧ True))) → (((p4 ∨ p5) → (((p5 ∨ (p3 → False)) ∧ p5) ∨ True)) ∨ (p4 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
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
theorem thm_5_vars_208530083998421911013941045648 : (((True ∨ p1) → (p5 ∨ (False ∨ True))) → (((p5 ∨ p4) ∨ ((p3 ∨ ((p2 → p2) → p5)) → p3)) ∨ ((((p4 ∨ True) ∧ p2) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_149157453923619318276901766468 : (((p2 ∨ p1) ∧ (p5 ∨ (p1 → (p4 → ((p1 → (p3 → (True → (((p5 ∧ p2) ∧ p4) → False)))) → p3))))) ∨ ((False → (True → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111961778165560343471278742282 : (((((p3 ∨ ((True → p3) → p2)) → (p5 ∨ p2)) → ((p4 → (((p1 ∧ p3) → p1) → ((False → False) → p3))) → p5)) ∨ p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117120914860418754698827206025 : (((p3 → p5) → (p3 ∧ (((p3 ∨ (p1 ∧ (p3 → ((p5 ∧ (p4 → True)) → (p3 ∨ True))))) ∧ ((p2 → p5) ∨ p1)) ∨ p1))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249495582506700451697060281289 : ((p5 ∨ p1) ∨ (((p4 ∨ True) ∧ (p4 → ((p5 ∨ p4) ∧ (False → p1)))) ∧ (p4 ∨ ((False ∧ ((p1 → True) → (p3 ∨ p1))) → (p2 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
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
theorem thm_5_vars_320014035822886941650374164758 : (p4 ∨ (((False ∨ p4) ∧ p4) ∨ ((((p3 ∧ p1) ∧ True) ∨ (((p4 ∧ ((p1 ∧ p1) → True)) → False) → ((True ∨ p3) ∨ (p3 ∨ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177950166902604943085941609543 : ((((p4 ∨ (True ∨ p2)) → ((((False ∧ p5) ∨ p3) → p4) → p1)) ∨ p2) ∨ (p2 ∨ (p5 → (((p2 ∧ p2) ∧ (True ∧ p3)) ∨ (False → p5))))) := by
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
theorem thm_5_vars_343480349067694866618176632879 : (p2 → ((p3 → p4) ∨ ((p1 ∧ (p5 → ((p1 ∧ False) ∧ (((((True → p2) ∧ p3) ∧ p4) ∨ ((p5 ∨ p4) ∧ (False ∧ p3))) ∨ p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119911830422641688023535342262 : (((((False ∨ (p5 ∨ p4)) → (False ∨ (True → (p5 ∨ (((p5 ∨ p5) ∨ ((False → p3) ∨ p3)) ∧ True))))) → (p1 ∧ p1)) ∧ p4) → (p3 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ (p5 ∨ p4)) → (False ∨ (True → (p5 ∨ (((p5 ∨ p5) ∨ ((False → p3) ∨ p3)) ∧ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
        -- True on the right can always be proven directly.
        apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h5
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245369528675089529186717068007 : ((p2 ∧ p3) ∨ (((((p2 → False) ∧ p2) → p2) → p3) → (p5 ∨ ((((((True ∧ False) ∨ p3) → (p2 ∨ p5)) ∨ p2) ∨ p1) → (p3 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → False) ∧ p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797454688649320840906322463370 : (((p1 → ((p4 ∨ ((False ∧ ((p5 → p4) ∧ ((((True ∨ p1) ∨ (p3 → False)) → True) → ((True → False) → False)))) ∨ (p4 ∧ True))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_46858288140332749772205989167 : ((((p2 ∧ (((((False ∧ (p2 ∨ ((p3 ∧ p5) ∨ p5))) ∧ p3) ∧ p4) ∨ (p4 ∨ (p3 ∨ (p1 ∨ p4)))) ∧ p5)) ∧ p5) ∨ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



