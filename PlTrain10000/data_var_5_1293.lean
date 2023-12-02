variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198644849202280643876349502090 : ((p3 ∨ ((p2 ∧ False) ∧ (False → (True ∧ True)))) ∨ ((True → ((p4 → (p3 ∨ p2)) → (p5 ∨ (((p5 ∧ p3) ∧ p5) → (p3 ∧ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158979293391179697150517838805 : ((p3 ∨ (((True ∨ True) ∨ (p5 ∧ (((p1 → False) ∧ p3) → (p5 ∧ False)))) ∧ (True ∧ (p2 ∧ False)))) ∨ ((False ∨ (p1 ∨ p3)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117228021572671293364118667648 : ((True ∧ ((p3 → p5) → (((False → ((p5 ∧ (p2 → p5)) ∧ (p3 ∧ (p5 ∨ p4)))) → (((p2 → p3) ∧ p1) ∨ p4)) ∨ p3))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40036080403443092241536265310 : (((((((True ∧ False) ∧ (True ∧ True)) ∧ (((((p3 → p5) → (p5 ∨ (True ∧ False))) → p4) ∧ p3) ∧ (False → True))) ∧ p2) ∧ p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351788664035193547229802438890 : (p4 → ((((p5 ∨ True) ∨ ((True ∨ False) ∨ (p1 ∨ p5))) → (p2 ∨ True)) ∧ (False → (p2 → ((True ∨ ((p3 ∨ p2) ∨ True)) ∨ (p4 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48225766004791699406078959956 : (((True ∧ ((((((False ∧ p2) → False) → (False ∨ ((p2 → True) ∨ True))) ∨ p4) ∨ (p4 → p1)) ∨ ((p4 ∨ p4) ∧ p3))) → (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625816626622579205346074144610 : ((((p1 → (p5 ∨ (True ∧ ((p4 ∨ ((p5 → p5) ∧ (p3 ∧ ((p5 → (p5 ∧ (True ∨ True))) → (p3 → (p3 → p4)))))) → p3)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51309075738454502830878605182 : (((p2 ∨ (p1 ∧ ((p1 ∨ ((p2 ∧ p4) ∨ (p4 ∧ p1))) → (p5 ∧ ((True ∧ p5) → p3))))) ∨ ((p1 ∨ False) → (False → (p3 ∨ p3)))) ∨ p5) := by
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
theorem thm_5_vars_251974739586603535441050191404 : ((p4 → False) ∨ ((p5 ∨ (((p2 ∨ (p3 ∧ False)) ∧ p3) ∧ ((((p1 → p5) → p5) ∨ p2) ∨ (p3 ∧ (p2 ∨ (p2 → True)))))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759304231863980555507954274313 : (((p2 ∧ ((p1 → ((p2 → p5) ∨ ((((p4 ∧ p2) → (p3 → (p4 ∨ ((p4 ∨ p5) → True)))) ∧ False) → (p1 → p3)))) → (p5 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172319360165032878821142617033 : (((p4 → ((p2 ∧ ((p1 ∨ p5) ∨ True)) ∨ p4)) → (True → (True ∧ (p2 ∧ False)))) ∨ ((True → (False → (p2 → ((p5 → False) → p2)))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111848746098290398392045260979 : ((((((False ∨ (p1 ∨ p5)) → ((p5 ∨ (((p4 ∨ p3) ∨ p2) ∧ True)) ∧ p2)) → (p4 ∨ p3)) → (p1 ∨ (p3 → p4))) ∨ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119289640711892676798613560042 : ((p3 → ((p4 ∨ ((p5 ∧ (p5 ∧ (p2 → (True → True)))) ∨ (((p3 → True) → (((p2 → p4) → p3) → p1)) ∨ p2))) ∨ False)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791811524718369142900652742632 : (((True → (((((((p3 ∨ p1) ∨ True) ∨ (p2 ∨ ((p5 ∧ (p4 ∨ p5)) ∨ True))) ∧ ((p1 ∨ p2) → p1)) ∨ p4) ∧ p3) ∧ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328098597482712558430554314438 : (True → ((((p2 ∧ ((p4 → (p4 ∧ (((p1 ∧ p3) ∨ (p3 ∨ p2)) → True))) ∧ p1)) ∧ ((p1 → True) ∧ p3)) ∨ p4) ∨ (p5 ∨ (False → False)))) := by
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
theorem thm_5_vars_303743719058803879526587525042 : (p1 ∨ (((((((True ∧ p3) → (p1 ∧ False)) ∨ ((p5 ∧ ((False → (False ∧ p1)) ∨ ((p1 ∧ p3) ∧ p5))) ∨ False)) ∧ p4) ∧ p5) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54212641035861100792979624092 : ((((p2 → ((p4 ∧ (p2 → p4)) ∧ p5)) ∨ p2) ∧ ((p1 ∧ (((p5 ∨ (((False ∨ True) ∨ True) ∨ p2)) → False) ∧ (p3 → p3))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187393352169713050172114832404 : ((p4 ∧ ((((p1 ∨ True) ∧ p2) → (p2 ∧ False)) ∧ (p1 ∨ p2))) → ((((p5 ∧ (p1 ∨ ((p4 ∨ (p2 ∧ p5)) → p5))) ∨ p3) ∨ p1) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∨ True) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344302767721939985125124088491 : (p2 → (p3 ∨ (((((p1 ∧ ((p3 ∧ p2) ∧ p2)) ∧ p2) ∨ (False ∧ ((((False → p4) ∨ False) → False) ∨ p5))) → p1) → ((p2 → p1) ∨ p2)))) := by
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
theorem thm_5_vars_613107400024962600713298397901 : (((((((((False ∧ (True ∨ ((p4 ∨ p3) ∧ p4))) → p1) ∧ p3) → ((p4 → (False ∧ p3)) ∨ (p3 → p1))) → p2) → (p1 → p2)) ∨ p2) ∨ p2) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((False ∧ (True ∨ ((p4 ∨ p3) ∧ p4))) → p1) ∧ p3) → ((p4 → (False ∧ p3)) ∨ (p3 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631319559320778854549642958045 : ((((((p3 ∨ (((p1 ∧ (((True → p1) ∧ p4) ∧ ((p1 → (p5 ∨ p2)) ∨ p4))) ∨ (p4 → p5)) ∨ (p3 ∧ p4))) → p4) → True) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115126198910587584499372225465 : ((((((p3 ∧ p2) → p3) ∧ p5) ∧ (p4 → (p2 → (False ∧ p2)))) → (p5 ∧ (((p3 → p2) ∨ (p4 ∨ (p5 ∧ p4))) → p4))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177630260522073798341334025389 : ((((((p4 → (p3 ∨ p1)) → (p1 ∧ (True → p5))) → p4) ∧ True) ∧ p3) ∨ (((p5 ∨ p4) ∧ (((p4 ∨ p5) ∧ False) → p1)) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752734192570356934971767893915 : (((False ∧ ((((p4 → p3) ∧ (p4 ∨ p3)) ∨ ((((True ∨ (p4 → (False ∨ p5))) ∧ p1) ∧ ((False ∧ True) → True)) ∧ (p4 ∧ p2))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206863471807424578455964555900 : (((((True ∧ p2) → p5) ∧ p2) ∧ p3) → (((((p4 → (((p1 ∨ (p4 ∧ p2)) ∧ p1) ∧ (p4 ∧ p5))) → p5) → p1) ∧ p5) ∨ (p2 ∧ p5))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165103754279439229114517535671 : (((False → (((((p2 ∧ True) ∨ p3) → (p3 ∨ ((p4 ∨ False) → p3))) ∧ p5) → p5)) → p4) ∨ ((p1 ∨ (((p2 ∧ p2) ∨ True) ∨ p1)) ∨ p1)) := by
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
theorem thm_5_vars_302997191465786370523125088947 : (False ∨ (p1 → ((((True → ((p1 → ((False ∧ (p1 → (p3 ∨ ((p3 ∨ False) ∨ p2)))) ∨ True)) ∧ p1)) → False) → p2) ∧ (True ∨ (p1 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True → ((p1 → ((False ∧ (p1 → (p3 ∨ ((p3 ∨ False) ∨ p2)))) ∨ True)) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68975704826207573286353227214 : ((p4 → (p4 → (p2 ∨ (((((((p4 ∨ (p4 ∧ p5)) ∧ p5) ∨ p2) ∧ p3) ∧ ((p2 → (p4 → (p4 ∨ p5))) → p1)) ∨ p3) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119075316117311623526969402112 : ((p1 → ((((((True ∨ p5) ∨ p2) → (((p5 ∨ p2) ∧ (p3 → p2)) → p5)) ∧ (True → p5)) ∨ True) ∧ (p4 → (True ∧ p4)))) ∨ (p4 ∨ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358034697464674316016404781285 : (p5 → (p1 ∨ ((((((False ∨ p2) ∨ (False ∧ p4)) → (True → (((True → True) → p4) → (p1 → p4)))) → True) → ((p2 ∨ True) → p3)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603916427742017840788638337933 : ((((p5 ∨ ((((True ∧ (p2 ∨ ((((((False ∨ p1) ∨ True) ∨ p1) → ((p4 ∧ p3) ∧ p4)) ∨ False) ∨ p5))) → p3) → p5) ∧ p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256882120052942666373484868718 : ((p1 ∨ p4) → (((((((p5 ∨ False) ∧ (True ∨ ((False ∧ p4) → p3))) ∧ p4) ∧ p3) ∨ p2) ∨ (((p1 → True) ∨ (p2 ∧ p2)) → True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336317163774386999179272285709 : (p1 → (((((p4 ∨ p4) → False) ∨ True) → (p3 ∨ ((((p2 ∧ (((p5 ∧ p1) ∧ True) → p3)) ∧ (p1 ∧ p2)) ∨ (True ∧ p4)) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353200578261157102409915260264 : (p4 → (p4 ∧ ((True ∨ False) ∧ ((p5 ∨ p3) ∨ ((p4 ∧ (((p4 ∧ (p2 ∨ ((p1 ∨ (p2 ∨ p4)) ∨ (p4 ∧ p2)))) ∨ p1) ∨ p4)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135399843884031571490346613073 : (((((p4 → ((p1 → (True ∧ False)) → (p1 ∨ p2))) ∨ p2) → ((True ∧ p3) ∨ (False ∧ False))) ∨ (p3 ∧ (p2 → False))) ∨ (p1 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692921907667319232583066726305 : (((((p3 → p1) ∧ ((p5 → True) → ((((p5 ∨ p2) ∨ True) ∧ p4) ∨ p1))) ∧ ((((p5 ∨ p5) → p2) → (p4 → (False → False))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111917166366061277888234589291 : (((((p5 ∧ p5) → (p1 ∨ ((((p1 ∨ p4) ∧ p1) → False) ∧ p3))) ∨ ((False ∨ ((p2 ∧ (False ∧ False)) → p3)) ∨ p2)) ∨ True) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41368647013856748123989867770 : (((((True → ((True ∧ p5) ∧ p2)) → ((False → p3) ∨ (((True ∧ p5) ∧ p5) → p2))) → ((((p3 ∨ True) ∨ p4) → p5) ∨ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264189944117810533949328217343 : (True ∧ ((((p2 ∨ ((p4 ∨ True) ∧ True)) ∨ p4) → p5) → (((True ∧ p1) ∧ True) ∨ (((False → ((True → p1) → (False → p3))) ∨ True) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∨ ((p4 ∨ True) ∧ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 ∨ ((p4 ∨ True) ∧ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45286930103116259056233281345 : (((p2 ∧ (((p2 ∨ (p3 ∧ p2)) ∨ p2) ∧ ((((p5 ∨ True) ∨ p3) → (False ∨ ((True ∨ (False → True)) ∧ (False ∧ False)))) ∧ True))) → False) ∨ False) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 ∨ True) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- False on the left can always be used.
          apply False.elim h17
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h15.left
          let h21 := h15.right
          -- False on the left can always be used.
          apply False.elim h20
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h5.left
      let h26 := h5.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h27 : ((p5 ∨ True) ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h28 := h25 h27
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h32.left
          let h35 := h32.right
          -- False on the left can always be used.
          apply False.elim h34
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h32.left
          let h38 := h32.right
          -- False on the left can always be used.
          apply False.elim h37
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h5.left
    let h41 := h5.right
    -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
    have h42 : ((p5 ∨ True) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h40, we can now drive its conclusion.
    let h43 := h40 h42
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- False on the left can always be used.
      apply False.elim h44
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- False on the left can always be used.
        apply False.elim h49
      case inr h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h47.left
        let h53 := h47.right
        -- False on the left can always be used.
        apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56454896068028520363700883715 : ((((p2 → False) ∨ (False ∧ p5)) → (p1 → (((p4 ∧ (p5 ∨ (p1 ∨ (p3 ∧ (True ∨ (False ∧ (True → p4))))))) ∨ (p1 → False)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112240236998441804214322406793 : (((p3 ∨ (((((False → False) ∧ (p3 → (p2 ∨ p2))) ∨ (p5 → (p3 ∨ (True ∨ (p1 ∧ p2))))) → (p5 ∧ p4)) ∨ False)) ∨ p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56273109571486156599448602452 : (((p4 → ((False ∧ p1) ∨ p3)) ∨ (((p1 → (((p5 ∧ p2) → (((p5 → p2) → (False ∨ p5)) ∨ (p2 ∨ True))) ∨ False)) → p3) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((p5 ∧ p2) → (((p5 → p2) → (False ∨ p5)) ∨ (p2 ∨ True))) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117784820222753866506122701874 : ((p4 ∧ ((((True ∨ False) ∨ p1) ∨ (p5 → (((p1 ∧ ((p5 ∧ p4) ∨ p4)) → p2) → p3))) → ((False ∨ (p2 ∧ False)) ∧ True))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184655164909779546483150510571 : ((((((False ∨ p5) ∨ False) → True) → p1) ∨ (p4 ∧ (p1 → True))) ∨ (p5 ∨ (((True → p5) ∧ False) ∨ ((p3 → (False → (p5 ∨ False))) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59785995372132417398469178192 : (((p2 ∧ p1) → ((False ∨ ((p4 ∧ p2) → False)) ∨ (((((False → (((p2 ∧ False) → (p1 ∨ False)) → p5)) ∨ True) ∨ p1) → p4) ∨ True))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659834919964356041010925502753 : (((((p5 ∨ ((True ∨ True) ∨ ((((True ∨ p3) ∨ (p4 → p3)) ∧ (((p2 ∨ p4) ∨ (p5 ∨ True)) ∧ True)) ∨ p5))) ∧ True) → (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65067957370044106782500789159 : ((p2 ∨ (p4 ∧ (((((p5 ∧ (((p5 ∧ ((p1 ∨ p1) ∨ (True ∨ (p3 ∧ False)))) → p2) ∨ p5)) → p2) ∨ p1) → p2) ∨ (p4 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149491697732318325422490101867 : ((p1 ∧ (((True ∨ (p4 → ((p5 ∧ p5) → True))) → ((p3 ∨ (True ∧ ((p3 ∨ p1) ∨ p2))) ∨ p3)) ∨ True)) ∨ ((p5 → (p3 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245727168225175884151776001030 : ((p3 ∧ p2) ∨ (((False → (True ∨ (p4 ∧ ((False ∧ p1) ∨ True)))) → ((p2 ∧ (p4 ∨ p5)) ∧ p4)) → (p2 → (True → ((p5 ∨ p2) ∧ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (False → (True ∨ (p4 ∧ ((False ∧ p1) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304999978979674383562621332702 : (p1 ∨ ((((((p5 → p1) ∨ False) ∨ (((p2 ∧ p1) ∨ True) ∨ (False ∧ (p4 ∨ p2)))) ∨ True) ∨ (p1 ∧ (p4 ∨ p2))) ∨ (p3 → (False ∧ False)))) := by
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
theorem thm_5_vars_137966221464257982185624886453 : ((p5 ∨ (((True ∨ (p2 ∨ False)) → (((p3 → True) ∧ (p3 → ((p1 → True) → p1))) ∨ p1)) ∨ ((p4 ∧ p5) → p2))) ∨ (True ∨ (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242973230408825587223357211693 : ((p4 → True) ∧ ((((False ∧ ((p2 ∨ ((p3 ∧ (((p3 → p3) ∧ (p2 ∨ p2)) → p4)) ∧ p4)) ∧ False)) ∧ (p3 → (p5 ∨ False))) ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191445809650000862032490046034 : (((False → p1) → ((((False ∧ True) → True) ∧ True) → False)) ∨ ((((p3 ∨ p4) ∧ (p3 → (p5 ∨ ((True ∨ p4) ∧ p3)))) ∨ True) ∧ (False → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338598361472835255548115204867 : (p1 → (((p1 → p1) → p3) → ((p2 ∨ (((((p5 ∧ p3) ∧ p5) ∧ p5) ∨ (True ∧ False)) ∨ p1)) ∧ (((p3 ∨ (p1 → p5)) ∨ p3) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647101067048895624174976439074 : ((((p3 → ((p2 ∧ (((p3 → True) ∧ p5) → p4)) ∨ (p3 ∨ (((p1 ∧ (p1 ∨ (((p1 ∧ p3) ∨ False) ∧ False))) → p4) ∨ p2)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53848743969002461044749083264 : ((((p5 → (False ∧ (p3 ∨ p2))) → ((p4 → p1) → p3)) ∨ (True → ((((((False ∨ True) ∧ p5) ∨ p4) ∧ p3) ∧ p4) ∧ (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317682755263576389568296688175 : (p4 ∨ (((p3 ∧ ((((True → p5) → p5) ∧ (p3 ∨ p1)) → (((False ∧ p4) → ((True ∨ (p4 → False)) ∧ (False → p5))) ∧ p3))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117604499988063721810522500785 : ((p2 ∧ (p5 ∨ (True → (((p1 → p5) ∧ p5) ∨ (p4 → ((True ∧ (p3 ∨ ((p1 ∧ (True → p3)) → True))) → (p3 ∧ p3))))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247559594361482536249365414274 : ((False ∨ p4) ∨ ((False ∨ (p2 ∨ p2)) ∨ ((p4 ∨ (p4 ∧ p1)) ∨ ((((False → (True ∨ (True ∧ p2))) → (p2 ∧ p4)) → (True ∨ p3)) ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324083749422127282216818335828 : (p5 ∨ ((((p3 ∧ p5) ∨ True) ∧ (((True ∧ (p2 ∧ False)) ∨ p5) ∧ True)) ∨ (((p5 → p5) ∨ (p4 ∧ True)) → (p3 → (True ∨ (p3 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114997206313126962476273438215 : ((((p5 ∨ ((p3 ∨ False) ∨ (True → p1))) ∧ ((p5 ∧ p2) ∧ p3)) ∧ ((((p4 ∧ (False ∨ p2)) ∨ (p2 ∧ p2)) ∨ True) ∨ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246425166918361819678591140965 : ((p5 ∧ True) ∨ (p1 → (p3 ∨ (p3 ∨ ((((p5 ∨ True) ∧ p5) → (p4 ∨ p1)) ∧ ((False ∧ ((p3 ∧ (p4 → p3)) ∨ (p4 → True))) → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71715369223370699080412445212 : (((p3 ∧ (((((p5 ∨ p5) ∧ (((p3 ∧ (p4 → p4)) ∨ (p1 → p4)) → False)) ∨ False) ∧ (p1 → ((p4 ∨ p3) → p3))) ∧ p3)) ∧ p4) → p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 ∧ (p4 → p4)) ∨ (p1 → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∧ (p4 → p4)) ∨ (p1 → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h20 := h12 h18
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45620892363645277332366622056 : (((p4 ∨ (((p1 ∨ (False → ((p4 ∨ True) ∨ p1))) ∧ (p4 ∧ ((((p4 ∧ p2) ∧ p1) → (True ∨ p2)) ∨ (True ∨ p2)))) ∧ p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329751752112485978146712235605 : (True → (True ∧ ((True ∧ (p4 ∨ (((False → ((p3 ∧ p2) ∨ p2)) ∧ p3) → ((True → (p2 ∨ p2)) ∨ (p2 ∨ ((p4 → p4) → p3)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706676345657378409506877010852 : ((((p5 → ((((p4 ∧ p5) ∧ True) → p4) ∧ True)) ∧ (p5 ∧ ((((p5 → (p3 ∧ p3)) ∨ p5) → p5) ∨ ((p3 → p3) ∨ (p2 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266134550726147008471744774540 : (True ∧ (p3 → (((((False ∧ p1) ∨ False) ∧ (p4 ∧ p5)) ∨ ((p4 → (True ∨ (p5 → (p3 ∨ (p2 ∧ False))))) ∨ p1)) ∧ (p4 → (p1 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205034084134616463829688842788 : (((p5 ∨ ((p2 ∧ p4) ∨ False)) → False) ∨ (p1 → (((p2 → ((p4 → p4) → False)) ∨ p3) → (((p5 ∧ (p5 → p3)) ∧ (False ∧ False)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117511660088815862911138909112 : ((p2 ∧ (((p2 → ((p2 → p5) ∧ (p5 → ((p5 ∧ (((p2 → (False ∧ p3)) ∨ p2) ∨ (p3 ∧ p4))) ∨ p5)))) → False) ∨ p5)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251378557059864087724378618673 : ((p2 → p4) ∨ (((p3 → (p4 ∧ (True ∧ (p3 → False)))) → (p1 ∧ p1)) ∨ (((((((p5 ∧ False) ∧ p4) → False) ∨ p4) ∧ False) → p5) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57034149829667544891561370441 : (((p2 → (True ∨ p1)) ∧ (((p5 ∨ (((p2 ∨ (((p5 ∨ (p5 → p5)) ∨ True) ∨ (p2 → True))) ∨ (p4 ∧ True)) → False)) ∨ False) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66686574276635396358236667965 : ((True → ((p3 → (p1 ∨ (True ∧ p5))) → ((p2 → (p1 → False)) ∧ (((p1 ∨ ((p5 → p1) → ((False ∧ p2) ∧ p2))) → p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599359462661311658279530693402 : (((((p3 ∧ p1) ∨ ((p5 ∨ ((((True ∨ False) → ((p3 → (p2 ∧ p5)) ∧ p2)) ∨ p1) ∧ ((p3 → (False ∧ p5)) ∧ p5))) ∧ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306021567117803248037725462403 : (p1 ∨ ((True → ((p3 ∨ p4) → p1)) ∨ ((((True ∧ p1) → False) ∧ p1) → ((((p1 ∨ False) ∧ ((p5 → (p5 ∨ p4)) ∨ p5)) ∧ p2) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : (True ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : (True ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761303266401179033134104727645 : (((p3 ∧ (((p5 → (((((False ∧ p2) → ((p4 ∧ ((p2 → (True → p3)) ∨ p2)) ∧ p4)) → (p1 → p5)) → True) ∨ p2)) → p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59289744586652128342734150951 : (((p3 ∨ p4) ∨ ((True → (((p3 ∧ (p5 ∨ (((p1 → p5) ∨ ((p3 → p2) ∨ True)) ∨ (p3 → False)))) ∨ p4) ∧ True)) ∨ (False → p1))) ∨ p5) := by
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
theorem thm_5_vars_42244883671942259831903324854 : (((False ∧ (p4 ∨ (((((((p3 → (p3 ∧ (p5 → True))) → p3) ∧ (False → (p3 ∧ p4))) ∧ p3) → (p2 ∧ p5)) ∧ p3) ∨ p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38158380216008070761963438295 : ((((((p4 ∧ (p2 ∨ p5)) ∨ (((p1 → p5) → ((p2 → p5) ∧ p4)) ∨ (False → (False → p1)))) → p3) ∨ (p2 ∨ (False ∨ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167048858418455100842440138139 : (((((p1 ∨ ((True ∧ p3) ∨ (((p5 ∨ False) → (p5 → p2)) → p3))) ∨ p5) ∨ p5) ∨ p4) → ((p1 ∨ (p2 → ((True → False) → p5))) ∨ False)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- Conjunctions on the left can always be decomposed.
            let h8 := h7.left
            let h9 := h7.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- Implications on the right can always be decomposed.
            intro h11
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h12 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h13 := h11 h12
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- Implications on the right can always be decomposed.
            intro h16
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h17 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h18 := h16 h17
            -- False on the left can always be used.
            apply False.elim h18
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h25 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h26
    -- Implications on the right can always be decomposed.
    intro h27
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h29 := h27 h28
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158736190205666985544417590612 : ((p3 ∧ (p4 ∨ (((p2 → ((False ∧ p5) → False)) ∨ (p5 ∧ (p2 ∧ True))) ∧ ((p1 ∨ p3) ∨ True)))) ∨ (p1 → (p1 ∧ ((p4 ∧ p3) ∨ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178112245934163229204710998570 : ((((((p2 ∨ (True ∨ (p4 ∧ p5))) → True) → p4) → (p1 ∧ p5)) → p1) ∨ (((True → ((p5 ∨ p3) ∨ (True ∧ p5))) ∨ (False → p2)) ∨ p3)) := by
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
theorem thm_5_vars_67505389808927946903920543959 : ((p1 → (((p5 → p5) → (p3 ∨ ((p3 → False) ∨ True))) ∧ (((p2 ∧ p5) ∧ (p1 ∧ (p1 ∧ (True ∧ p4)))) ∨ ((p1 ∧ p1) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135742060706361453316171046892 : ((((p2 ∧ ((p2 → (False ∧ p5)) ∨ (p1 → p3))) → ((p3 → False) ∨ p4)) ∨ ((((p3 → False) ∨ p3) ∧ p4) → p1)) ∨ ((True ∨ p1) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147947103171408167050718014910 : ((((p2 ∨ p4) → ((p3 → False) → (((p4 ∨ (p2 → True)) ∨ False) ∧ ((p4 → p2) ∧ True)))) ∧ (p3 ∧ p1)) ∨ (((p4 ∧ p4) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41305087476729649321597638516 : ((((((p5 ∧ (p1 ∧ ((p4 ∧ True) → (False ∧ p4)))) → (p3 ∨ (True ∧ True))) ∧ p3) ∧ ((p1 ∧ ((p3 → p5) → True)) → p4)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261410249906367883136656264855 : ((p5 → p1) → ((p5 → p4) ∨ ((((p2 ∧ (True ∧ (p1 ∨ (False ∧ p2)))) ∨ p3) ∨ p2) ∨ ((p2 ∧ ((p4 ∧ p1) ∧ (False ∧ False))) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656856802291647381268071123225 : ((((((p4 → p4) → (p4 ∧ False)) ∧ ((p3 → (p2 → False)) ∧ ((((p4 ∧ p3) → (False ∨ (True ∧ False))) ∧ p2) ∨ False))) ∨ (p3 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148673159424928209442239433375 : (((((p2 → True) → ((p2 ∧ p5) ∨ p4)) ∨ False) ∨ (True ∨ (((p1 ∨ (p4 ∨ (p5 ∨ False))) ∨ True) → p3))) ∨ (p3 ∨ (False → (p1 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177701019632109472235995924141 : ((((((p2 ∧ ((p2 → p1) ∧ p2)) ∧ p3) ∧ p4) → (True ∨ p3)) ∧ p1) ∨ ((p5 ∧ (p3 ∧ (p3 ∨ ((True → (p2 ∧ p5)) ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61220765804850051836126670868 : ((False ∧ (False ∧ (((p1 ∧ (p2 ∨ (False ∨ p1))) ∨ p2) ∧ ((((p5 ∧ False) ∨ False) ∧ (True → (True ∧ (p4 → p1)))) ∧ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717890231506289612168637558340 : (((((p1 ∨ (p4 → p3)) ∧ p2) ∨ (p1 ∧ ((p4 → (p3 ∧ ((((False ∨ p2) → p1) ∧ p2) → p3))) ∧ (p5 ∧ (True → (True → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147931250949420411997517108353 : (((((p5 ∧ ((p2 ∨ p3) ∧ p3)) → p1) → ((p3 ∨ (False ∧ (True ∧ (p5 ∧ p1)))) → False)) ∧ (p5 → False)) ∨ (False → (True → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112771881514663581085027206438 : ((((p4 → (((p2 → (p3 → p5)) ∧ p2) → (False → p2))) → ((p3 ∨ (p4 ∧ (p4 ∨ ((p5 ∨ False) → True)))) ∧ False)) → p2) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (((p2 → (p3 → p5)) ∧ p2) → (False → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165482248465767087374495846967 : (((((p2 → p5) ∧ ((True ∧ (False → True)) → p1)) → p2) ∨ (p5 ∨ ((p2 ∧ p1) ∧ True))) ∨ ((p1 ∨ (True → (p2 ∨ (False → p2)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614662485223471414668714416802 : ((((((((True → False) ∧ (p4 ∨ (p2 → (p4 ∧ ((p4 ∨ True) ∨ p5))))) ∨ (p2 ∨ p3)) ∧ p1) ∨ (False ∧ (True ∨ (p5 ∧ p4)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112019278421376629404927743077 : (((((p2 ∧ False) → p1) ∧ ((((((p4 ∧ (p3 ∧ p1)) ∧ p2) ∧ True) ∧ p2) ∨ (((p1 ∧ p2) ∨ p1) ∨ p5)) ∨ p4)) ∨ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767757193680440479854188940908 : (((p5 ∧ ((((((((p4 → p2) ∨ True) ∧ ((((p3 → (p4 ∨ p3)) → p5) → (p1 ∧ p3)) ∧ p3)) → p5) ∧ p3) ∨ p3) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55404972441267016904080712016 : ((((((True ∨ p2) ∨ True) ∨ p1) ∨ p4) → ((p4 → (p3 → (((p2 ∧ (p1 ∨ p3)) ∨ ((p4 ∧ p2) ∨ p4)) → p4))) → (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44825935431869542498802832158 : ((((p4 → (False ∧ p3)) ∧ (p5 → ((True ∨ True) ∨ ((p3 → (True ∧ (False ∨ ((p5 ∧ (p1 ∧ False)) ∨ (p2 ∧ True))))) ∨ True)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



