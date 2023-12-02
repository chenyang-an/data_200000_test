variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111909726555532137877047184705 : ((((((False → p3) ∨ True) ∨ (((p3 ∧ p2) ∨ (p5 ∨ p5)) → p2)) ∧ (((((False → p1) ∧ p2) ∧ p2) ∧ p4) ∧ p5)) ∨ p2) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703411022297116161232842674582 : ((((p2 ∨ (p2 ∧ ((p5 ∧ (p1 → (p4 ∧ False))) ∧ False))) ∨ (((((True ∧ (True → p5)) → False) ∨ p4) → (False ∧ (p1 ∧ True))) → True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_353536068087685477367738043611 : (p4 → (p3 ∨ ((True → (p1 → (((p3 ∧ (((p3 ∧ p5) ∨ ((True ∧ p4) → (p5 ∨ (p3 → (p1 ∨ p4))))) ∨ p3)) ∨ p4) ∨ p5))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219933060457070745149517272960 : ((p4 → (p5 ∨ (p1 ∨ p3))) → (((((p2 → (p4 → p5)) ∨ (p4 ∧ (p1 ∧ (p2 ∨ (True ∨ p5))))) → p4) ∨ ((p2 → p1) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605157891342171851127438376907 : ((((p2 → ((p1 ∧ (p2 ∧ ((True ∧ (p3 ∨ p3)) ∧ True))) ∨ (((((False ∧ (False ∨ (True ∧ p3))) ∧ False) ∧ p1) ∨ False) ∧ p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111574650010460130522455795465 : (((((p2 ∨ False) ∨ (((False ∨ p1) → p5) → ((((p2 ∧ (p2 ∧ ((p4 → p5) ∧ p2))) ∨ p5) → True) ∧ p1))) ∧ True) ∨ True) ∨ (p2 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177313127191234308872770823910 : ((p2 ∨ ((((p1 ∧ False) ∨ (p5 → p4)) ∨ (p3 ∧ True)) ∨ (True → True))) ∧ ((((False → p2) → False) → ((p4 → (p2 ∨ p3)) ∨ p5)) ∧ True)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148549597071053804937555950153 : (((((True → True) → ((p2 ∨ (False ∧ p1)) → p4)) ∨ p3) ∧ (((True ∧ False) ∨ (p4 ∧ (True → True))) ∧ p5)) ∨ ((p1 ∧ (False ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191755041203073804689493824750 : ((False ∨ (True → ((p2 ∨ (p5 ∨ False)) ∨ (p1 ∨ True)))) ∨ (((p3 → False) ∨ p1) → (p3 ∨ (((p3 → (p3 ∨ p1)) ∨ p4) → (p4 ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_152435868933390564516628400559 : ((((True → p4) ∨ True) ∧ ((((p2 ∨ (p4 → (p3 ∧ (p5 ∧ (p5 ∨ p2))))) ∨ (p3 ∨ p2)) → p3) → p1)) → ((p5 ∧ p2) ∨ (False → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161737539801604260514776792654 : ((p3 ∨ ((p5 → p2) ∨ ((p2 ∨ p4) ∨ (p2 → (((p4 ∧ p1) ∨ True) ∨ ((p5 → p3) → p3)))))) → (p1 → (((p1 → False) ∧ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138205419154432146957765919059 : ((p2 → ((((p3 ∧ p4) ∧ ((True ∧ p5) ∨ (((p3 ∧ (False → p4)) ∧ ((False ∨ p1) ∧ p4)) ∨ p3))) ∧ p1) ∧ p5)) ∨ (True ∨ (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68228032512898898120562098542 : ((p3 → ((((p3 ∨ (p1 → ((True ∨ p5) ∧ p4))) → (False ∨ ((p2 → p4) ∧ p4))) ∧ (p4 → ((False ∨ (True ∧ p3)) ∨ p4))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950041403214764051200414801102 : (((((True ∨ p1) → False) ∧ ((((((p1 ∨ (p2 → p2)) → p1) ∧ p2) ∨ True) → (((False → (p3 ∨ (p5 ∨ False))) ∨ False) ∨ p4)) ∨ p1)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342150082989502586862242803196 : (p2 → ((((p4 ∧ p1) → (p5 ∧ ((((p1 → (True ∧ p1)) → p3) ∧ (p1 → (p3 → p1))) ∨ p1))) → p1) ∨ ((p5 ∨ (False ∧ p5)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14460405905433968634805030891 : ((((((p1 ∧ (p1 → ((p2 ∨ p4) ∧ ((p2 ∨ (((p2 ∨ True) → False) ∧ p4)) ∨ p5)))) ∧ p5) ∧ (p3 → p4)) ∧ p1) ∨ (p1 → p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47684402338789238932627855536 : ((((p1 ∧ (((p5 ∨ (False → p5)) → p5) → (p1 ∨ (p1 → (((p1 ∧ (False ∧ p4)) ∨ (p5 ∨ True)) ∧ p2))))) ∧ True) → (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26654819730450078896490754909 : (((p3 ∧ p4) ∨ ((p5 ∧ False) ∨ ((p3 ∧ (p3 ∧ (p5 ∧ (((p3 → (((p3 → (True ∨ True)) ∨ False) ∧ p5)) ∨ p2) → p4)))) → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 → (((p3 → (True ∨ True)) ∨ False) ∧ p5)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247284937684016506449564503357 : ((False ∨ False) ∨ ((((p2 → ((((p4 → p1) ∧ ((((True ∨ p2) ∧ ((False → p3) → p4)) ∨ p3) ∧ p4)) ∨ False) ∨ True)) ∨ p2) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600198588916821863995653810428 : (((((False → p5) → (((p3 → (((p5 ∨ True) ∨ True) ∨ p1)) ∨ (p2 ∨ p1)) → ((p2 → (p2 ∧ (False ∧ (p4 ∨ p1)))) ∨ True))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615753805975029146801111899723 : (((((p2 ∨ ((((p2 → p1) ∨ False) ∧ (p3 → (p2 ∧ p2))) → (p4 → p5))) ∧ ((((p1 ∧ False) ∨ (p2 → p4)) → p2) ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208051023201636518674969383346 : (((True ∨ (p5 → p5)) ∨ (p5 → p3)) → ((((p4 → True) ∨ p3) ∧ (((((p5 ∧ p2) ∧ (p5 ∧ p1)) ∨ p2) → (p2 ∧ False)) ∧ p4)) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_662342754802167483270802788618 : (((((p2 ∧ ((False ∧ (p2 ∧ (p1 ∧ p5))) → True)) ∧ (((p4 ∨ ((p1 ∨ ((p2 ∧ p2) ∧ False)) ∧ False)) ∧ p5) → True)) → (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769842842078041331223606684044 : (((p5 ∧ (p5 ∨ ((((False → (((True → (p1 → False)) ∨ p3) ∧ (p2 ∧ (p1 ∨ (p3 ∧ ((p5 → p2) → p4)))))) ∧ p5) ∨ False) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172675265942520020511578714520 : (((p4 → p5) ∧ ((p3 ∧ (False ∧ p3)) ∧ ((True → ((p1 ∧ p4) ∧ p1)) → p3))) ∨ (p5 ∨ (((False → p5) ∧ p5) ∨ (p2 → (p3 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672000043122713781728883424843 : ((((((p1 ∧ (p5 ∧ (p1 ∨ (((p5 ∨ ((p4 ∧ p5) → (p3 ∧ p3))) ∨ (p3 → False)) → True)))) → p2) ∨ p4) → ((p5 → p4) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221293677616179721689605032074 : (((p3 ∨ p3) ∨ True) ∧ ((p4 ∧ p1) ∨ ((p4 ∧ (((p5 ∨ (p4 ∨ p2)) ∧ (False ∨ ((p5 ∧ p5) ∧ p5))) ∧ p3)) → (p2 ∨ (p4 ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h16
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183892587557179069486767206306 : ((((p2 ∨ p4) ∧ ((p2 ∧ ((False → True) ∧ False)) ∨ p4)) ∧ p1) ∨ ((True ∨ True) ∧ ((((p2 → p5) ∨ (True ∨ (p1 ∧ p5))) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40141321454551867616062145752 : (((((p1 ∧ (((((p3 → (p1 → p5)) → p2) ∨ True) → p1) ∨ (p3 ∧ (p4 → False)))) → ((p5 ∧ (p3 ∧ p1)) ∧ p3)) ∧ p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301196947496943132367132019765 : (False ∨ ((p2 → (((False ∨ p4) ∧ False) ∨ (p4 ∧ False))) → (p3 → ((((p4 ∨ (True ∨ p1)) → p4) ∨ (p4 ∧ (p2 ∨ p3))) → (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ (True ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158315119482916339002792242175 : (((p2 ∨ (p4 ∧ True)) → (((p1 → (((False ∧ p3) ∨ False) ∧ p2)) ∨ True) ∨ (True ∨ (p3 ∧ True)))) ∨ (p2 → (((p5 → False) ∨ p3) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36181790940521224766458101369 : ((p3 → (p3 → ((False ∧ ((p2 ∧ (p1 ∧ (p1 ∨ p3))) ∨ p5)) ∨ (((p1 ∧ (p2 ∧ (True ∨ p5))) ∨ ((True ∧ True) → p3)) ∨ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622473994286860119493658715286 : ((((p3 ∧ (p2 ∧ (p2 ∨ ((((p5 ∧ p1) → (p5 → ((p3 ∧ (p4 → p5)) → True))) ∨ (p1 ∨ False)) ∧ ((p5 ∨ p1) ∨ p1))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256820386811830813148312452664 : ((p1 ∨ p3) → (((p3 ∨ (False ∨ (p1 ∨ (((False ∨ False) → p5) ∨ ((((True ∨ ((p5 ∨ True) ∨ p2)) ∧ p2) ∧ p4) ∨ False))))) → p1) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Conjunctions on the left can always be decomposed.
              let h13 := h12.left
              let h14 := h12.right
              -- Conjunctions on the left can always be decomposed.
              let h15 := h13.left
              let h16 := h13.right
              -- Disjunctions on the left can always be decomposed.
              cases h15
              case inl h17 =>
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h18 =>
                -- Disjunctions on the left can always be decomposed.
                cases h18
                case inl h19 =>
                  -- Disjunctions on the left can always be decomposed.
                  cases h19
                  case inl h20 =>
                    -- One of the premise coincides with the conclusion.
                    exact h2
                  case inr h21 =>
                    -- One of the premise coincides with the conclusion.
                    exact h2
                case inr h22 =>
                  -- One of the premise coincides with the conclusion.
                  exact h2
            case inr h23 =>
              -- False on the left can always be used.
              apply False.elim h23
  case inr h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226207451702824268966374057867 : (((p2 ∨ p1) ∨ p5) ∨ ((True → (p1 ∧ p2)) → ((((p4 ∨ ((p2 ∨ ((False ∨ p4) ∧ (p3 ∧ p1))) ∨ p1)) ∨ p2) ∨ (p2 → p3)) ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338254990590860897240964545883 : (p1 → ((p1 → ((p5 ∨ (False → p1)) → p3)) ∨ ((p5 ∨ (p4 → ((p3 → (((p2 ∨ p3) ∧ ((False ∧ False) → True)) ∧ p2)) ∨ True))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263398399406040276765076986746 : (True ∧ ((((p4 → p4) ∧ (p1 ∧ (True ∧ ((p4 → p2) → (p2 ∨ p1))))) → ((((p2 ∨ p5) ∨ p2) ∨ True) ∨ p3)) ∨ (p2 → (True → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_303929686964160508429986696082 : (p1 ∨ (((((p1 → (p1 → (False → True))) ∨ p1) → p1) ∨ ((p1 → (p2 → ((p5 → ((p4 → p4) ∧ (p5 → p3))) ∨ p2))) ∨ p3)) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254889070148755630431379628026 : ((p4 ∧ True) → (((((p5 ∨ p3) → (p3 ∨ True)) ∧ ((p3 ∧ p2) ∧ (p1 ∨ False))) ∨ (p2 → (False → (False ∧ (p3 ∧ False))))) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305313684304885667132261106922 : (p1 ∨ ((p3 ∧ (p5 → ((p5 ∧ (p5 ∨ ((p4 ∨ (p5 → (p5 → p1))) ∧ (p1 → p1)))) → p3))) ∨ (p3 → (p3 ∧ (True → (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760201657366970015362385800174 : (((p2 ∧ ((p1 ∨ True) ∧ ((((p4 → ((p1 ∧ True) ∧ (p2 → True))) ∨ ((p1 → p4) → p2)) → p4) ∧ (((p1 → False) ∨ True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661768032391013706401390822115 : ((((((p3 ∧ (p2 ∧ (((p3 → (p1 → p1)) → ((p4 → p2) ∨ p2)) → p5))) → p2) ∨ (p4 ∨ (p4 → (p4 → False)))) → (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111661899680774128584159758511 : ((((p5 ∧ ((p4 ∨ False) → (p3 ∨ (p1 ∨ (((p1 ∧ True) → ((p2 ∧ (p2 → p5)) → p4)) ∧ (True → p5)))))) ∨ p1) ∨ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39697286713409683786664207650 : (((p4 ∨ (p1 ∧ (True → ((((True ∧ (p3 ∨ (p5 → (False ∧ (((p3 ∧ p4) ∨ (p2 → p4)) ∧ True))))) → p3) ∧ p3) → p4)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766670078675204880856524062729 : (((p4 ∧ (False ∨ (((((True ∨ p5) ∨ (True ∨ (p1 → (p1 ∧ p5)))) → ((((False → p1) ∧ p5) → p4) ∧ (True → p2))) ∧ p4) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171313845104643034705885270640 : ((((((((p2 ∨ p3) ∧ (p2 ∧ p3)) → (False ∨ False)) → p1) ∧ p1) ∨ p1) ∧ p2) ∨ ((p4 → (p4 → (True → ((True ∧ p2) → p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46724659179939134718328972583 : (((True → ((p2 → ((((((False ∧ p1) ∧ (p3 ∧ (p5 ∨ p3))) → (p1 ∧ False)) ∧ p4) ∨ p3) ∨ (p1 ∨ p3))) ∨ False)) ∧ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171502369890307153378396505356 : ((((((((True ∨ ((p5 → p1) → p1)) ∨ p2) → False) ∧ p2) ∧ p2) ∧ p5) ∨ p2) ∨ ((p4 ∨ ((p3 ∨ ((True → p5) ∨ p3)) ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45358503515107082576286227168 : (((p4 ∧ (((False ∨ p5) ∧ ((((p4 → p2) → (((False ∧ False) ∨ p3) → (p1 → False))) → p2) ∨ p3)) ∨ (p2 → (p4 → p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190769901311202682101921788212 : ((((False ∨ (p1 ∧ (True ∨ p2))) ∧ p4) ∨ (p3 → p1)) ∨ (((p3 → p2) ∧ p1) ∨ ((False → (p3 ∧ False)) ∨ (p4 → (p4 ∨ (p4 ∨ p5)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134957203393332067729178764602 : (((((p4 → (p5 ∧ (False → p3))) ∨ (p4 ∨ (p1 ∨ (p1 ∨ p3)))) → ((p3 → p1) ∨ (p1 ∧ p2))) ∧ (False ∧ p1)) ∨ (p4 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67423882790451051197128780901 : ((p1 → (((p3 → ((((False ∧ p5) ∨ (p1 ∧ True)) → p5) ∧ ((p2 → False) ∧ ((p4 → p3) ∧ (p1 → p3))))) ∨ False) → (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55940894276239480548451170207 : (((p3 → ((False ∧ p4) → p3)) ∧ (((((True ∧ ((p5 → (p2 ∧ p3)) → p1)) ∧ p1) → p4) ∧ p5) ∧ (((p2 ∨ False) → p3) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43582896300611120105444513414 : ((((((((((p4 ∧ (True ∧ True)) ∨ True) ∧ (p5 ∨ True)) → ((p2 ∧ p1) → (p2 → p3))) ∧ p2) → (p4 ∧ p1)) ∨ p2) → True) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808724347582382298393179140462 : (((p4 → (p3 → (((p2 ∧ (((False → p5) ∨ (p1 ∧ (False → False))) → (((p3 → ((p2 ∧ False) ∧ p4)) → False) ∧ p2))) ∧ True) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675502009533006826428998921398 : (((((p3 → ((p2 ∨ (True ∧ p4)) ∨ (p2 → (((False ∧ (p2 ∨ p1)) → (True → p3)) ∨ p1)))) → p1) ∧ ((p3 ∨ p3) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43495334111197450309739873962 : ((((p5 ∧ ((((p1 ∨ (True ∨ True)) ∨ p3) → p2) ∧ (p4 ∨ (p4 ∧ (p5 ∧ (True → ((p3 ∧ p2) ∧ (p3 → True)))))))) ∨ False) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593032492774901654686713915497 : ((((((((((p4 → ((p3 ∨ p4) ∧ p1)) → p4) ∨ p1) → ((False ∧ (p3 ∧ p5)) ∨ False)) → p2) ∨ p1) ∨ ((False → p5) → p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42299639707310921445052938185 : (((p2 ∧ ((True → (p1 → (True ∨ ((True ∨ p4) ∧ ((p4 ∧ ((((p4 ∨ p2) → p1) ∧ p1) → p5)) ∨ (p1 → p4)))))) → False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54930689737742807485570953404 : ((((True ∨ ((p4 → p2) ∧ p2)) → p4) ∧ ((True → (((False ∨ p5) ∧ p1) ∧ p5)) ∧ ((p4 ∨ (p5 ∨ (p5 → p4))) → (p5 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204322777228996132489163917420 : (((p3 ∧ ((False ∧ p2) ∧ False)) ∧ p2) ∨ ((p1 → p2) → (((p1 ∨ p2) → ((p4 → (p2 ∧ (p2 ∨ p4))) ∨ (p2 ∨ p5))) → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54405105144977844443699689392 : (((((p3 ∧ False) ∨ ((True ∨ p3) ∨ False)) ∧ p5) ∨ (p1 ∨ (False ∨ (((False ∨ p5) ∧ p5) → ((p4 ∨ ((True ∧ p4) ∧ p5)) ∨ True))))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50594779226290240979026695904 : (((((True ∧ p5) ∧ (((((p5 → (p3 → p1)) ∧ p3) → p1) → False) → (p4 ∨ p2))) ∧ (p1 ∧ p5)) → ((p1 → (False ∧ True)) ∨ p5)) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231820680905639442771509603240 : (((p5 ∧ True) → False) → ((p4 ∧ ((((True ∧ (p1 ∧ p3)) ∧ (p3 ∧ ((p4 ∨ ((True → True) → p2)) ∧ p3))) ∨ p1) ∨ p5)) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902950132567527833040871964877 : (((((p3 → p4) ∨ (p5 → (((False → False) → p3) → (False ∧ (p4 ∨ (False → (p2 ∧ (True ∨ p4)))))))) ∧ (p2 ∧ ((p2 ∨ p1) → p4))) → p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173747698536022821019842522749 : (((((False → (p1 ∧ p4)) ∨ (p5 ∨ p5)) → ((False → (p3 → p3)) ∨ p3)) ∨ p1) → (p2 ∨ ((p2 → p2) ∧ ((p5 ∨ (p2 ∨ True)) ∨ True)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193107487966961488457356007297 : (((p2 → (p1 ∨ (True ∨ p5))) ∧ ((False → p4) ∨ False)) → ((True ∨ (False ∨ (((p2 ∧ True) ∧ p3) ∨ p1))) → (p3 → (True ∧ (p4 ∨ p3))))) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103326168976463845827133752828 : (((p4 ∨ (((True ∨ (False → (True ∧ p2))) → ((((True → (p4 ∧ p1)) ∧ True) ∨ (False → p2)) ∧ p5)) ∨ (p3 → p3))) ∨ True) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159546106915075797885411552914 : (((p4 ∧ (p4 → (((p1 ∨ (p4 → False)) ∧ ((p3 ∨ (p5 ∨ p1)) ∨ False)) ∨ (p1 ∧ p3)))) ∧ p4) → ((p1 ∨ p1) ∧ ((p5 → p4) → True))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h21 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h22 := h18 h21
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
            have h25 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h18, we can now drive its conclusion.
            let h26 := h18 h25
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h30
  -- Implications on the right can always be decomposed.
  intro h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214155948796938849275604422642 : ((((p1 ∧ False) → p3) → p3) ∨ ((p3 ∧ p1) ∨ (((p4 ∨ ((p3 ∨ ((True ∧ False) → p5)) ∨ p4)) ∧ p3) → ((p1 ∧ True) ∨ (p1 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165415093051944862869086322009 : ((((p4 → ((((p1 ∧ (p5 → True)) ∧ p3) → True) → p4)) → p4) → ((False ∧ p2) ∧ p5)) ∨ ((((True ∨ p2) ∨ (True ∧ False)) ∨ False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342430210578065847450424898546 : (p2 → (((p5 ∨ False) ∨ (p4 ∨ (((p3 ∨ ((p5 ∨ p5) ∨ p4)) ∨ (p3 → True)) ∧ p2))) → (p3 ∨ ((p2 ∨ p3) ∨ (p5 → (False ∧ p5)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h1
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227827318677400695462401623690 : ((p2 ∧ (p3 ∧ True)) ∨ (((True → (p4 → (True ∧ p5))) ∨ (p4 → (p3 ∨ (p1 ∧ ((((False ∨ p2) → (p3 ∨ p5)) → False) → p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684820785817129288814396846041 : (((((p5 ∧ p4) → (False ∨ ((p1 ∨ ((p4 → (False ∧ p5)) ∨ (p5 ∨ p1))) → (p2 ∨ p3)))) ∨ ((False ∧ ((p1 ∨ p2) ∨ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121669321400416020222270634284 : ((((((p4 ∧ (False → p3)) ∨ (False → False)) ∧ ((p1 ∨ p1) ∨ True)) ∨ (((p1 ∨ (False → p4)) → p1) → (p2 → p5))) → p5) → (p3 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ (False → p3)) ∨ (False → False)) ∧ ((p1 ∨ p1) ∨ True)) ∨ (((p1 ∨ (False → p4)) → p1) → (p2 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244430845227512620951601830534 : ((False ∧ p2) ∨ (((((p3 ∨ (p2 ∧ p5)) ∨ p5) ∨ (p1 ∨ (False → (p2 → (True ∧ ((p3 ∧ ((p3 ∨ False) ∨ True)) ∧ False)))))) ∨ p4) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44115014260097419094863467494 : (((((p5 ∨ ((((p5 ∨ p4) ∧ ((p1 ∧ (p2 ∨ p1)) ∨ p1)) ∨ (p4 → p5)) ∧ True)) → (p4 → p1)) ∨ ((p1 ∨ p5) ∨ p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206134882329683662768866051893 : ((p4 ∧ (p5 ∧ ((True ∧ p3) → True))) ∨ ((p3 ∨ p3) → (p2 ∨ (((p3 ∧ False) ∨ ((p1 → ((p1 ∧ p3) ∨ (True → p5))) ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_354864149641322693300360055798 : (p5 → (((p4 → p5) → (((p1 ∨ p5) → False) ∨ (((((p1 → p3) ∧ p1) ∨ (p2 ∧ p2)) → p3) → (((p5 ∧ p1) ∧ False) → p4)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732358329670436304572375964724 : ((((False ∧ p1) ∧ (p5 → (p2 ∧ ((((p3 ∨ (False ∧ (((p4 ∧ (True ∨ p1)) → (p1 ∧ p4)) → p4))) ∨ p3) ∨ p3) ∧ (p5 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179087684288033555769696132860 : ((False ∧ (((((p1 → p2) → (p3 → (p1 → True))) → p2) ∨ p3) ∧ p2)) ∨ ((p3 ∧ p4) → (p2 → (((p4 ∧ (p4 ∧ p1)) ∧ p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43629671336573956955888488159 : ((((((True ∧ (p2 ∨ (p5 ∨ p4))) ∧ ((p2 ∨ (p1 ∧ p5)) ∨ ((False ∧ (p4 ∨ p3)) ∨ (False → True)))) ∧ (p4 ∧ p5)) → p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183979346973949006638969311251 : ((((((p2 → p4) ∨ (p4 → (p3 ∧ False))) ∧ p2) ∧ True) ∨ p5) ∨ ((p5 ∨ ((p3 ∨ p5) → ((False ∧ False) → (False → p1)))) ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602140383098073798867783987806 : ((((p5 ∧ ((((True → p5) ∧ p2) ∧ p1) ∨ (p4 ∨ (((False → (True → p1)) → (p3 ∨ True)) ∧ (((p5 ∧ p4) ∧ p5) → p2))))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118107410483164862046941788440 : ((False ∨ ((p2 ∧ ((p1 ∧ ((True ∨ (((p4 ∨ True) ∨ p1) → (p4 → (p3 ∧ (False ∨ p1))))) ∨ (p5 ∧ p3))) → p5)) ∨ True)) ∨ (p4 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54035818822173250428923999064 : ((((((False → (True ∨ p4)) → p5) ∧ True) → (True ∨ p2)) → ((p5 ∧ ((True ∨ ((((True ∧ p5) ∧ p5) → p5) ∨ p1)) ∨ p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60476664759394465599198134765 : (((p5 → p5) → (((p3 ∧ (False → ((p3 → (p4 ∧ p3)) ∧ (p4 ∧ p1)))) ∨ ((p1 ∨ p1) → True)) ∧ ((p2 → p5) → (True ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38371737847315675118559241397 : ((((False ∧ (((p2 ∧ (p4 ∨ p4)) ∨ ((p1 ∧ (p3 → p5)) ∨ (p2 ∧ p3))) → p1)) ∨ ((p5 ∧ (p3 ∧ (False ∨ True))) → True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647961624779107502509138880415 : (((((((p3 → ((False ∧ (True ∧ ((p3 → (False → (p1 → (p1 ∧ p5)))) → p4))) ∨ p1)) → p2) → (p1 ∨ p3)) ∧ True) ∧ (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137763816207844675873613122199 : ((p2 ∨ (((True → p3) ∨ (p1 ∨ ((p5 ∨ ((((True ∨ p2) ∨ p2) → True) → (p5 ∧ False))) ∨ p2))) ∨ (p2 ∨ p4))) ∨ (True ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137611811065914773513442913618 : ((False ∨ (((p5 ∧ (False → ((((p5 ∧ p5) → (False ∧ (p1 → p5))) → (p4 → p5)) ∨ p3))) ∧ (p5 ∨ False)) ∧ False)) ∨ (p3 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118655910773500359756364582275 : ((p4 ∨ (p5 ∧ ((True ∨ True) → (p3 ∨ ((False ∨ p3) → ((p4 → False) ∧ (((p4 → p4) ∧ (p3 ∨ p4)) → (False → p3)))))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327223347311753703729388292242 : (True → ((p2 → ((((p3 ∧ True) → (True ∨ (False ∨ p2))) ∨ (p2 → (p1 ∨ (p5 → (p4 ∨ (p4 ∧ ((p4 ∧ p3) → p3))))))) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683704120931063557482766903280 : (((((p2 ∨ (((p4 ∧ ((p4 ∧ (p1 → (p3 → p2))) → (p4 ∨ p5))) → p4) ∧ p5)) ∧ True) ∨ (True ∧ (p4 ∧ ((True ∧ p4) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47120461510536370549541368415 : ((((True → ((p3 ∨ (p2 → False)) → (((True → False) ∨ (p3 ∧ (p2 ∨ p5))) ∨ (False ∧ p3)))) ∨ ((p2 ∧ p5) → p5)) ∨ (p4 ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114837211433460099835090507223 : ((((((p5 ∨ p1) ∧ (p3 ∧ ((p3 ∧ False) → (False ∨ False)))) ∧ p3) ∧ p4) ∨ (True ∨ (False → ((False ∧ (p4 ∧ False)) ∨ False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345461648003760284368066352492 : (p3 → (((p5 ∨ ((p1 ∧ p5) ∨ (((True ∧ p5) → (p5 → (False ∧ (p4 ∧ (p2 → p5))))) ∨ (p3 ∨ (True ∨ p1))))) → (p2 ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234945372141486531933856068395 : ((True ∧ True) ∧ (True → (((p3 ∨ True) ∧ (((p2 ∧ False) ∧ p2) → p5)) → (p4 ∨ ((p5 ∨ p5) ∨ (p4 ∨ (((p3 ∨ False) ∧ p4) → p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328838424503632428801760156021 : (True → ((p3 → (((p3 → p3) → ((p3 → p4) → p5)) ∨ p5)) → ((p4 → p5) → (p1 → ((p3 ∨ p5) ∨ (False ∨ (True ∨ (p2 ∧ p5)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160358635881607309395536482638 : ((((p3 ∧ (p4 → ((p1 ∨ p5) ∧ (True → ((p4 ∨ True) ∧ True))))) ∨ p5) ∧ (p1 ∧ (p2 ∧ p2))) → ((p5 ∧ (True → (p1 ∧ False))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



