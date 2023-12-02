variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351909906527191157361087136031 : (p4 → (((p3 → (p3 → (p4 → p4))) → ((True ∨ p1) → p1)) ∨ (((False ∨ p4) → ((((p5 → (p3 ∧ p5)) ∨ p2) → False) ∧ False)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317642472029147690124334832948 : (p4 ∨ (((p1 ∧ (p4 ∧ ((p5 → False) ∨ (False ∨ (p1 → ((p1 ∧ (((p2 → p1) → (p5 ∨ (p2 ∨ p5))) ∧ p3)) ∨ p5)))))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68765806484298482053392055361 : ((p4 → ((p2 ∧ (((p4 ∧ p1) ∨ (((p2 ∧ p3) ∧ p4) ∨ p2)) ∨ p1)) ∨ ((True ∨ ((p5 ∨ (p1 → (p1 → p4))) ∧ p4)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181682235130377559776895761806 : ((p4 → (True ∧ (True → ((((p1 → (False → True)) ∧ p3) → False) ∨ False)))) → (p5 → ((p1 ∨ (p3 → ((False ∨ p3) → (False ∧ p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64359211331212006723490128593 : ((p1 ∨ (((p2 ∧ ((p3 → (p4 ∨ p5)) → (False ∨ (((((False ∨ False) ∨ p4) ∨ p2) → (True ∧ p2)) ∧ p3)))) → (p3 ∧ p5)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654105238513585922316132928447 : ((((((((False ∨ p3) ∨ ((((p1 → (p2 ∧ p4)) ∧ ((False ∨ p2) ∧ p2)) ∧ p1) ∧ (p1 ∨ p5))) ∧ False) ∧ False) ∨ True) ∨ (p1 ∨ p2)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114577602485484672969188717337 : (((((p2 → p5) ∨ (((False ∧ p5) ∨ p3) → p4)) ∨ ((False ∨ (p5 ∨ True)) → False)) ∧ (((p2 → (p5 ∨ p3)) ∨ False) ∨ True)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_101893904888730304256173399712 : ((((((p5 ∧ True) ∨ p1) → (((p4 ∧ (p3 → (True ∧ False))) ∧ (((True ∧ p1) ∧ False) ∨ p1)) → (p5 ∧ False))) ∨ True) ∧ True) ∧ (True ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614091941957180645440841422028 : (((((p3 ∨ (((p4 ∧ ((p1 → p5) → (p5 ∨ (((p1 → p2) → p1) ∨ p5)))) ∧ p3) → (False ∧ p5))) ∨ ((p2 ∧ p3) ∨ True)) ∨ p3) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_57717412161801916025905307725 : ((((True ∨ True) → False) → ((((p3 → p2) ∨ ((p3 → p2) ∨ p5)) ∧ (p1 ∨ (False ∧ (p3 ∨ (True ∧ (p1 ∧ p4)))))) ∨ (p5 → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216920021440134497173258690976 : (((p5 ∨ (p3 ∨ p1)) ∧ p1) → ((p3 ∨ (p1 → (((((((p5 ∧ p5) ∧ (p4 ∨ p4)) → False) → p4) ∨ p3) → p2) ∨ (False → p1)))) ∧ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110777611413707195546654502507 : ((((((p1 ∧ p3) ∧ ((p4 ∨ p1) ∧ ((p2 ∧ p3) → (((False ∨ False) ∧ p2) ∨ (True ∧ (p4 ∧ p1)))))) ∧ p1) ∨ p3) ∧ True) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151840416429470486617592796393 : (((((False ∨ (True ∨ (p3 → (((True ∨ p1) → p5) ∨ p3)))) ∧ p2) ∨ True) ∨ (p1 ∧ (True ∧ (p5 ∨ p5)))) → (((p1 ∧ p5) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165930652643384899898349205581 : (((p4 ∧ p2) ∧ (((p1 ∨ (True → p1)) ∧ ((p4 → False) ∨ p2)) → ((p4 ∨ p4) ∨ p3))) ∨ ((True → (p5 → (p5 ∨ (p5 ∨ p3)))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63935237797359933742298251777 : ((False ∨ ((((p2 ∨ (p3 → (((p3 ∨ p2) → False) → p1))) → (p1 ∧ ((p2 → p5) ∨ (True → p2)))) ∨ (p1 ∨ (p5 → True))) ∨ p1)) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191475412383432763262124109329 : ((True ∧ (((p4 ∨ p3) ∧ ((p3 ∧ True) → p2)) → False)) ∨ ((p5 → True) ∨ (p1 ∧ (True ∨ ((p3 ∧ (True → p1)) ∨ (p1 → (p4 ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172980699711141055423661927437 : ((p4 ∧ (p4 ∨ ((((p3 ∧ p2) ∨ (p5 ∨ ((p3 ∧ p5) ∧ False))) → p1) ∨ p5))) ∨ ((p5 ∧ (p1 ∧ ((False → False) → p1))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62318861260273762666594011751 : ((p3 ∧ ((p1 ∨ ((p1 ∨ (p5 ∨ p5)) → (p2 ∨ (p5 ∨ ((((p5 → True) ∧ (True → True)) → True) ∨ (p5 ∧ p3)))))) ∨ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349297878707242465870845162631 : (p3 → (p2 → ((((p3 ∧ (p4 ∧ (p5 → (p5 → p3)))) ∧ False) ∨ p3) → (((p3 → ((p5 ∨ p1) → False)) → ((p4 → p1) ∧ p5)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32596529343992718708024241982 : ((p2 ∨ (((p2 ∨ True) → (p4 ∨ ((False → p2) → p4))) ∨ (((p2 ∨ ((p4 → ((p4 ∧ False) ∧ p4)) ∧ (p3 → p1))) ∨ p1) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820610053062746689656547138638 : ((((((p5 ∧ ((((((p5 ∨ p5) → p4) → ((True → p4) → p2)) → False) → p3) ∨ p1)) ∨ p5) → ((True → (p3 ∧ p2)) ∧ p4)) ∧ p5) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ ((((((p5 ∨ p5) → p4) → ((True → p4) → p2)) → False) → p3) ∨ p1)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157819317289291138534623185149 : (((((p2 ∨ ((p5 ∧ p1) ∨ p4)) → p3) → ((False ∧ p1) → False)) → (p3 ∨ ((p5 ∨ p1) ∧ False))) ∨ (p4 ∨ ((p2 → p4) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_165716200284952674901018761433 : ((((True → p4) ∨ (False ∨ p4)) ∧ (p2 ∨ (((((p1 ∧ p5) ∧ p2) ∧ p3) ∧ p2) ∨ p2))) ∨ (((False → p3) → ((p1 ∧ False) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135848834474802473910535519906 : (((p1 → ((p4 ∧ p4) ∨ ((p2 → (p4 ∧ False)) ∨ (p1 ∧ False)))) ∧ (((p1 ∨ p2) ∨ p4) ∧ (p4 ∨ (p3 → False)))) ∨ (True ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166139042592565785514870388258 : ((True ∧ (p4 ∧ (((p3 ∧ (True ∧ True)) ∧ ((True ∨ p3) → True)) → (p2 ∨ (p2 ∨ p2))))) ∨ (p2 → (True ∧ ((p5 → p2) ∨ (p2 ∨ p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63286923760184312258295460053 : ((p5 ∧ (((p5 → p3) ∧ False) ∧ (((False ∧ (((p4 ∨ p2) → p5) → (((True → True) ∧ (False → p5)) ∧ p4))) ∧ (p3 → p5)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627665237269586573493170670677 : ((((((p1 → (((((((True → p5) ∨ True) → True) ∨ p4) ∨ ((p2 ∨ p2) ∧ False)) ∨ p2) ∧ True)) ∧ (p3 → (False ∨ p2))) ∧ p5) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232074231521323811141046418264 : (((p4 ∨ p2) → False) → (p3 → ((p5 ∧ (((True ∧ True) ∧ ((((p4 → p5) → (p3 ∧ ((p4 ∨ p5) ∨ p4))) ∧ p5) → p4)) ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197103026268628852504754569590 : (((p5 ∧ ((p5 ∧ (p1 ∨ p4)) → p4)) ∨ p2) ∨ (((p3 ∨ True) → (p4 ∨ (True → False))) ∨ (p3 → (p5 ∨ ((p5 ∧ (p2 ∨ False)) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136461712724424742431948099212 : (((p3 → (p4 ∧ (False ∨ p3))) → (False ∨ ((p4 → (((p2 ∧ True) ∨ p5) → p5)) ∧ (p5 → ((p2 ∨ p1) ∧ p5))))) ∨ (False → (p5 ∧ p3))) := by
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
theorem thm_5_vars_60436678733207258035458721733 : (((p4 → p5) → (((p5 ∨ p3) ∨ (False ∨ (p1 ∨ (p1 → (p2 ∨ (p1 ∧ (p4 → ((p1 → p4) ∨ (True ∧ p2))))))))) ∧ (p3 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231584537274410241094419694003 : (((True ∧ True) → False) → (((((((p1 → (p5 → True)) → p4) ∧ p1) ∨ ((p5 → p5) ∧ p1)) → (p4 ∧ p3)) ∨ p2) ∧ (False ∨ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149111082137142027880447003971 : (((p5 → (p5 → p2)) → (((p5 ∧ p5) ∨ ((p5 ∨ p2) ∨ False)) ∨ (((p4 ∨ True) ∧ (False → False)) → False))) ∨ (True ∨ (p5 ∧ (False ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69180664832239500258520461097 : ((p5 → ((((((False ∨ False) ∨ p3) ∨ p2) ∧ (p1 ∨ True)) ∨ (p3 ∧ (True → True))) ∨ ((True ∧ (p1 → (p2 → (p4 → False)))) ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233317333567782363180560585376 : ((True ∨ (True → p1)) → ((((True ∧ False) ∨ p1) ∨ ((((p3 → True) → p3) ∧ (p4 ∨ p2)) ∨ False)) ∨ ((p5 ∨ p4) ∨ (True ∨ (p4 ∧ True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340838606818491497361443420334 : (p2 → (((p5 ∨ ((p5 ∨ True) → (((((((p2 ∨ p3) → p1) ∧ p1) ∧ p3) → ((p3 → p4) ∧ p1)) ∧ p4) ∧ True))) → (p4 → p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355626765528810277263459525985 : (p5 → ((p2 ∨ ((((((((p1 ∧ p5) ∨ p5) → ((p3 → (p3 ∧ True)) → (p1 ∧ p2))) → True) ∧ p2) → p4) ∨ p5) ∧ p5)) ∨ (p5 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141481971927094634884123591862 : (((p3 ∨ (True → p5)) ∧ (True → ((p4 ∧ ((p5 ∧ ((p4 → ((p5 → (p1 → p4)) ∧ p3)) → False)) ∧ p4)) ∨ True))) → (p2 → (p5 ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49247073864470220280382316494 : ((((p4 → p2) → ((False ∧ p5) ∧ (((True → (True → p4)) ∧ ((p1 ∧ (p3 → p4)) ∧ (p5 ∨ p5))) → p4))) ∨ (p3 ∨ (p3 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39946737674957188221756757546 : (((p4 → ((((((p3 ∧ (p1 ∨ (p3 ∨ (p4 → ((p4 ∨ p4) ∨ p2))))) ∨ p4) ∧ (p3 ∧ p4)) ∨ (p1 ∧ p3)) ∧ True) ∨ True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719052810739368221494261633288 : ((((True ∧ ((p3 → p5) ∨ p2)) ∨ (((((p5 → False) ∧ True) ∨ True) → (p4 → (False ∨ False))) ∨ (((p4 ∧ p2) → (True ∧ True)) ∨ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115173258710183890737590467209 : ((((((p3 ∧ p5) ∨ ((p3 ∨ p4) ∨ p3)) ∧ p2) → p3) ∧ ((((p5 ∨ False) ∧ (p1 ∨ p2)) → ((p4 ∨ True) → p2)) ∧ p1)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153688834669402846278015895272 : ((p2 → ((p2 ∨ p1) ∨ (((p5 ∨ ((p2 ∨ True) → p3)) ∨ ((False ∧ False) ∨ True)) ∧ ((p3 ∨ p5) → p4)))) → ((p4 ∧ (p5 → p3)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134499728107722755357976863204 : ((((((p2 ∧ ((p1 ∨ p1) ∧ ((p2 ∨ p4) ∨ p4))) → p5) ∨ (((p5 → p2) ∨ p3) → (p2 → False))) ∨ p3) → False) ∨ ((p2 ∨ p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689701349946113475246665530820 : (((((False → ((p2 ∨ False) ∧ p5)) → (p3 → ((((p4 ∧ p3) → p2) ∧ p5) ∧ p3))) ∨ (((p2 ∧ ((p4 → False) ∨ p2)) → p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166069176706136891111593446331 : (((True ∨ True) → ((((p4 ∧ p1) ∧ p3) ∨ (p1 ∨ ((False ∨ p2) ∧ (p5 ∧ p1)))) ∨ True)) ∨ ((p3 → (False ∨ (p4 ∧ (p2 → p2)))) → False)) := by
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
theorem thm_5_vars_260487991232973624697435209282 : ((p3 → False) → (((p4 ∧ (p2 ∧ (p1 ∨ (p4 → False)))) ∨ (True ∧ p2)) ∨ ((((False ∧ p4) ∧ p3) → p5) ∨ (((p2 ∨ False) ∧ p4) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158958927578664694879041567309 : ((p2 ∨ (p1 ∨ ((p3 → (p3 ∨ ((False ∧ ((True → True) ∧ False)) ∨ True))) → ((False ∨ p2) ∨ p5)))) ∨ (p2 ∨ ((True ∨ p4) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_161452519988531703195421770871 : ((p3 ∧ (((False → (True → p4)) ∧ ((p4 ∨ True) ∧ (True ∧ ((p1 ∨ (p4 ∨ p2)) ∧ True)))) ∧ p4)) → (True ∧ (False ∨ ((p4 → p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h9.left
    let h24 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h28
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h31
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h33
        -- One of the premise coincides with the conclusion.
        exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324503823663209926337678999522 : (p5 ∨ ((p2 ∧ ((p4 ∨ p2) ∨ p1)) ∨ (((p4 ∧ p1) ∧ (((True ∧ True) ∧ (False ∧ p1)) ∨ p5)) ∨ ((p3 → (p5 ∨ (p5 → True))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727091938732738901210097931421 : (((((p5 → p2) → p3) ∨ ((p3 → ((p1 ∧ ((p2 → (True ∨ p5)) ∨ ((p2 ∨ p5) ∧ p4))) → (p2 ∧ ((p4 → True) → True)))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_198353541901467629315033106895 : ((p2 ∧ (p3 ∧ (((p1 ∧ True) ∨ p5) ∨ p4))) ∨ (False → (p1 ∧ (False → ((p2 ∧ False) → ((((p4 ∧ (False ∧ True)) → p5) ∨ False) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148990791629143385287221498243 : (((p3 ∨ (p4 ∨ p1)) ∧ (((((((p5 ∨ p3) ∧ True) ∧ True) ∧ p2) → p5) ∧ (False ∧ (p5 → False))) ∨ p5)) ∨ (True ∨ ((p3 ∧ p3) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675258992295022197492972781414 : (((((p2 ∨ ((p3 ∨ ((p5 ∧ (False ∧ p1)) ∨ (False ∨ ((p1 ∧ p1) → (True → True))))) → p2)) ∨ p3) ∧ (p2 → (p4 → (False → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346294284102086476459619243025 : (p3 → ((((p4 ∨ ((p5 ∨ ((((p3 ∨ (p3 → p2)) → False) → ((False ∧ p4) → False)) ∨ False)) ∧ True)) ∧ (p5 ∨ False)) ∨ p2) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16809162267407879403132123067 : (((((p1 ∧ (p2 ∨ p1)) ∨ (p5 ∨ p5)) → (((False ∧ (((True ∨ p3) ∨ (p5 → p2)) → p2)) ∨ True) ∧ p3)) ∨ (True ∨ (True → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639600796546260450016450979000 : ((((((p3 → p3) → p5) ∧ ((p2 ∨ (p3 ∨ p2)) → (True ∧ ((p2 → ((p3 → True) → ((p1 ∧ p3) ∨ (True → p2)))) → p4)))) → p5) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657874319861589955761814510620 : ((((False ∧ (p5 ∨ ((((p2 → (((False ∨ p3) ∧ p2) → p5)) → (p4 ∧ (True ∨ (p2 ∨ True)))) ∨ p1) ∧ (p1 ∨ True)))) ∨ (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651728733023328512824197919021 : (((((p4 ∨ p3) ∨ (p1 ∧ (((((p2 ∧ (False → p3)) → p4) ∧ p5) ∧ (p1 → ((p3 ∧ (False → p1)) → False))) → p2))) ∧ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224133196138387356329094944988 : ((p5 ∨ (p4 → True)) ∧ ((p3 ∨ (True ∧ ((((False ∨ p2) → p4) ∧ (False ∧ p2)) ∨ p3))) ∨ (((((p1 → p5) ∧ p2) ∧ False) ∨ p2) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112650942362132892527188755673 : (((((p4 ∧ (((p2 → p2) ∧ (p4 → (p5 ∧ (p3 ∨ p4)))) ∧ p2)) ∨ ((True ∧ False) → p1)) ∧ ((False → p4) ∧ p5)) → p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164562540129928018799702417808 : ((((((p2 ∧ p5) ∨ p3) ∨ False) ∨ ((p4 ∧ (True ∧ p5)) ∧ ((p3 ∧ p1) ∨ False))) ∧ True) ∨ (p2 → ((p5 → (False ∨ p1)) → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136394119154449878237811874520 : (((p4 ∧ (False ∧ (p5 ∧ p5))) ∨ ((((True ∨ False) → False) → p4) ∨ ((p2 → (p4 ∨ ((False ∧ p1) ∧ p3))) ∨ p5))) ∨ (p2 ∨ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234393182312129915868923900995 : ((p1 → (p1 → p3)) → (True ∧ (p4 → ((False ∧ ((p2 ∨ (p2 ∨ p4)) ∧ (True ∧ ((p5 ∨ p5) ∨ p2)))) ∨ (True ∧ ((p2 → False) → True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42659973372579491491995788895 : (((p4 ∨ ((((p5 ∧ (p2 ∧ p5)) ∨ (p5 → ((False → False) → (p3 ∨ (p1 ∧ p4))))) ∧ p3) → ((p5 ∨ (p5 ∨ False)) ∨ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726096398720291363776071615268 : (((((p1 ∧ p4) ∨ p3) ∨ ((((p5 → (p4 ∨ p2)) ∧ ((((((p5 → p4) ∨ p2) → p5) → False) ∧ p4) ∨ p2)) ∧ True) ∧ (True ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788821865420103308532652175689 : (((p5 ∨ ((p2 → (((p1 ∧ ((p5 ∧ p3) ∧ ((p4 ∨ p5) ∨ p4))) → p2) ∧ ((p1 ∨ p3) → ((p4 ∨ False) ∧ (p1 ∨ False))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325099822092771276341124203373 : (p5 ∨ ((p2 → p3) → ((p4 ∧ (p3 ∨ ((((p3 ∨ (((p5 → True) ∨ p1) ∨ p5)) → False) ∧ p2) ∧ (((False ∧ False) ∧ p5) ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698235043132137979336369979247 : (((((p2 ∧ ((p4 ∨ (p4 → p2)) → (p4 → (p5 ∧ True)))) → False) ∨ (True ∨ (((p3 → ((False ∧ p2) → (p2 → True))) ∨ p2) → p5))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_172164756035002873430467306223 : ((((True ∧ ((p1 ∧ (p4 → p5)) ∧ p3)) ∨ (p2 → p5)) ∨ ((False ∧ True) ∨ False)) ∨ (((p3 ∨ True) ∧ (p2 → True)) ∨ ((p2 ∧ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45151030668666179358916917046 : (((True ∧ ((((((p5 ∨ ((True → p2) ∧ p3)) → ((p4 ∧ (False ∧ p4)) ∨ (p4 ∧ p1))) → (p2 ∨ p3)) → p3) → p3) ∨ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95665872680541889918277355576 : ((p5 ∧ ((p5 → (p5 ∨ p3)) → (((p3 ∧ p4) → p3) ∧ (((True → p2) ∧ (p3 → False)) ∧ (p4 ∧ ((p4 ∨ (p5 ∧ p1)) ∧ False)))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p5 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326985950822819126606381820199 : (True → ((((p1 ∨ ((False ∨ p3) ∧ (((p1 ∧ False) ∧ p2) ∧ p2))) ∨ (False ∨ ((p5 → p4) ∧ (p2 → p2)))) → (True ∧ (p5 ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687162973411418144254751543091 : ((((p3 → (p1 ∨ ((False ∨ p2) → ((False ∧ p3) ∨ ((((True ∨ p4) ∧ False) → p5) ∨ p4))))) → (p1 ∨ ((p5 ∨ (p2 ∨ True)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675584186294395873074393123730 : ((((((True → (p4 ∨ ((False ∨ p5) → ((((False → p3) ∨ p1) ∧ p4) ∨ p4)))) ∨ p2) ∨ (True → p2)) ∧ (False ∨ ((p2 ∧ p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686876824599899764041042076203 : ((((True ∨ ((((p4 ∨ (False ∧ True)) ∧ p1) ∧ p4) → ((True ∨ (p2 ∧ True)) → (p3 → p1)))) → ((p5 ∧ p4) ∨ (p5 ∨ (p1 → p1)))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_948165618069376552917254762635 : ((((True ∨ ((True ∨ p5) ∧ p3)) → (((p5 ∨ ((False ∨ (((True ∧ p3) ∨ p3) → (True ∨ p4))) ∨ False)) ∧ p5) ∧ ((p1 ∧ True) ∨ p3))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((True ∨ p5) ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171375019724624010817057090658 : (((((p4 ∧ (True ∧ (p2 → (False ∧ p3)))) ∧ p2) ∧ (p1 ∨ (p3 ∧ p4))) ∧ p4) ∨ (((p1 → ((False ∨ p5) → (p1 ∨ p3))) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14565688518825726029750700117 : (((((p1 ∨ p4) ∧ ((False ∧ p1) ∧ (((p1 ∨ (p5 ∧ (((p4 ∨ p3) ∧ (p1 → p1)) ∧ True))) ∧ False) ∨ False))) ∨ p1) ∨ (p2 → True)) ∧ True) := by
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
theorem thm_5_vars_740851383189013508573739743060 : ((((p3 ∨ False) ∨ (p2 ∧ (((p4 → p2) → (True → ((True → (p5 ∨ ((p3 ∧ True) → True))) ∨ p3))) ∧ ((False ∨ (p2 → p3)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114882574310967052455059919227 : ((((p2 ∨ p4) → ((p3 → (p1 ∧ (p5 ∨ ((p4 ∧ p2) ∨ p5)))) ∧ p2)) ∨ (p2 ∧ ((p3 → p5) ∧ ((p1 ∧ False) ∧ p3)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172292926468453329135789816295 : ((((((True → (p4 ∧ p2)) ∨ p2) ∧ p3) ∨ p4) → ((p1 ∨ (False ∨ p2)) → False)) ∨ ((True ∨ p5) ∧ (p1 ∨ ((True → False) → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115513573623376819537010521876 : ((((p1 ∧ (p2 ∨ p1)) ∧ (p4 → (p4 ∨ p3))) → (((((False → p5) ∧ p5) ∧ p3) ∧ p2) ∨ (((p1 → True) ∧ p4) → p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18857809108594646201677818180 : (((((((True → True) ∧ p3) → p5) → False) ∨ ((p5 ∧ ((p1 ∨ p5) ∨ True)) → (p2 ∨ p5))) ∨ ((((False ∨ p4) ∧ False) → p5) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49154327296563863110927326997 : ((((p1 ∧ (((True ∧ True) ∨ (True → p3)) → False)) ∨ ((((p4 → True) ∨ ((p1 → p1) ∨ p5)) ∧ True) ∧ p5)) ∨ (p3 ∧ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41793836217547849770686006272 : (((((p4 → True) ∨ (p3 ∧ True)) → ((p3 ∨ True) ∧ (((((p5 ∧ (p3 ∧ p3)) → p4) ∧ p5) ∧ (p5 ∨ (p3 → p4))) ∨ p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635372112583682877335551687243 : ((((((((((False ∧ True) ∧ p2) ∨ p5) → p4) → p4) ∨ ((((p1 ∧ True) ∨ p4) ∧ p1) → p1)) ∧ ((p5 ∧ (p3 → p4)) → p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86096335117174023840584919956 : (((p3 → ((((True → p2) → (p3 ∧ True)) ∨ p4) → p2)) ∧ (p4 ∧ ((((p1 ∨ p4) → (False ∧ False)) ∧ ((p1 ∧ True) → p1)) ∨ p2))) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751599899031787600730853622089 : (((True ∧ (p2 ∧ ((((p5 ∨ ((p1 ∧ True) ∨ (p4 ∨ p2))) ∧ True) → ((p2 ∧ ((False ∧ (p4 ∨ p4)) ∨ p5)) → (p2 ∨ p3))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592658853806505568387510426949 : (((((p1 → (((p5 ∧ p2) ∧ (True → (p5 ∨ p2))) → (((True ∨ ((p4 → False) → False)) ∨ (p1 ∨ True)) ∨ p4))) → (False ∧ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780745764079851547354601822563 : (((p2 ∨ ((p5 ∨ ((p4 ∨ (p3 ∨ False)) ∧ p1)) ∨ ((((((True ∧ False) → p4) → p4) ∧ (p1 → ((p5 ∧ p5) ∧ p2))) ∨ p5) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185611917127218927786844260910 : ((True → ((p5 → ((p5 → (True ∨ (False ∨ p4))) ∧ p4)) ∨ p3)) ∨ ((p4 ∨ ((False → True) ∨ ((p2 ∨ p4) ∨ (p4 ∧ (p5 ∧ True))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_600499016987388110909958067 : (((p4 ∨ (False → (((((False → (p5 ∧ ((p5 ∧ False) ∨ True))) ∨ (p5 ∨ p2)) ∨ False) → p3) → ((p1 → True) ∨ p3)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337174169442143601160436690853 : (p1 → (((((((p4 ∨ False) → ((False → p5) ∧ True)) ∧ (((p3 ∧ (True → (p3 → False))) ∨ p4) ∨ p5)) → p3) ∧ True) → p3) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228550482701298670341008978613 : ((p1 ∨ (p5 ∧ p3)) ∨ ((p2 ∧ (p4 ∧ (p4 ∧ ((True ∨ (((p3 ∨ p3) ∧ (False ∨ p3)) ∨ False)) ∧ (p2 ∨ p4))))) ∨ (p4 → (True ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906856877852152970726996820136 : ((((((p1 ∨ ((p3 ∨ (p4 → (p2 → (True ∨ p3)))) → p1)) ∨ (False → p1)) ∨ ((p1 ∨ p5) ∧ p5)) → (False ∧ (p4 ∨ (False → True)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ ((p3 ∨ (p4 → (p2 → (True ∨ p3)))) → p1)) ∨ (False → p1)) ∨ ((p1 ∨ p5) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317781888421051903095974988177 : (p4 ∨ ((((p3 ∨ p1) → (((p2 → ((False ∧ False) ∧ p3)) → p1) ∧ p1)) ∨ ((True ∧ ((False ∧ (p5 → p5)) → p3)) ∨ (False ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811241649714553001215484379558 : (((p5 → (p5 ∧ ((p3 ∧ (((p2 → (False ∨ True)) ∨ ((p3 ∨ p4) ∨ p5)) → (p2 ∧ False))) ∨ ((p5 ∧ (False → p3)) ∨ (False → False))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357035253719881549159295880750 : (p5 → ((p4 ∧ (True ∨ True)) ∨ ((True ∨ p3) → (p5 ∧ (((True → (p2 ∧ ((((p1 ∨ (p5 → p4)) ∨ p3) → p5) ∧ p3))) → p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762397431646187330591353875875 : (((p3 ∧ ((((p2 → True) → p2) ∧ (((((p1 ∨ p2) ∨ p2) → True) ∨ (p1 ∧ ((p1 → p1) ∨ p2))) ∧ p1)) → (p3 ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



