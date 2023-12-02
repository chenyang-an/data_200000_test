variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962393717569024896904683122748 : ((((True → False) ∧ ((p1 ∧ ((((True ∨ p1) → (False ∨ (((p5 ∧ (p4 ∨ (p4 ∨ (p5 ∧ p5)))) ∧ p4) → p4))) → p5) → p1)) ∧ p1)) → p5) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336077456812997051335522011330 : (p1 → ((((True → ((True ∨ (((False ∨ ((p1 ∨ p4) → (p5 ∨ (p4 ∧ p4)))) ∧ (p2 → False)) ∧ p1)) → p3)) ∧ (p2 → p5)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186447593545209464330490587373 : (((((((p3 ∧ p3) ∧ p1) ∨ p5) → p1) ∧ p3) ∧ (p1 → p5)) → ((((p5 ∨ (True → False)) ∧ p4) ∨ (((p4 ∨ True) ∧ p3) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694491002922865195155497444398 : ((((True ∧ (((p1 ∨ (True ∨ (((True → p2) → p3) → p3))) → p2) ∨ p4)) ∨ ((p1 ∧ p4) ∨ ((p3 → (p4 ∨ p3)) → (True ∨ p2)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_314103855238014903344471957962 : (p3 ∨ ((((p4 ∨ p3) → (True → p4)) ∧ ((p2 ∧ (p4 ∧ (p2 → p3))) ∧ ((p5 ∧ True) → (((False → p1) → p2) ∧ True)))) → (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477543082228942102409500511621 : (((((p5 ∧ (True ∧ (p2 ∨ (p1 ∨ (p4 ∨ p2))))) → p3) → (p2 → ((False ∧ ((p1 ∨ (p1 ∨ (False ∧ p3))) ∧ p4)) ∨ (True ∨ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152486966646741450593429241023 : ((((True ∨ p4) ∨ True) ∨ (p1 ∨ ((((p4 ∧ (p1 ∨ ((p4 ∨ p4) ∨ (True ∨ p3)))) ∨ p4) ∨ False) → True))) → (p5 → ((True ∧ p3) ∨ p5))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
theorem thm_5_vars_300543279710242731468146589266 : (False ∨ (((False ∨ ((False ∧ (p4 ∧ p3)) → ((p5 ∧ (p3 ∧ ((p5 ∧ p1) ∨ True))) → (p2 → p1)))) → p1) ∨ (p5 ∨ ((True ∧ p3) → True)))) := by
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
theorem thm_5_vars_728886245930697164200047789086 : (((((p5 ∧ p1) ∧ True) → ((((False ∧ True) ∧ p2) ∨ ((p2 ∨ ((p1 ∨ (p1 ∨ (False ∨ p1))) ∨ p1)) ∧ (p1 → (False ∧ True)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936953703535139588350886073471 : ((((((True ∨ True) ∨ (p2 ∧ p2)) → p5) ∧ ((p3 ∧ p5) → ((p3 ∧ (((((p5 ∧ p3) ∧ True) → True) ∧ (False → True)) → True)) → p4))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ True) ∨ (p2 ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927233837271861485685849817714 : (((((((((True ∨ p2) → True) → p3) → p1) ∧ p3) ∧ True) ∧ (True → (((((False → p2) ∨ (False → False)) ∧ False) ∨ (p5 ∨ p5)) → True))) → p1) ∧ True) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (((True ∨ p2) → True) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172773255752095330157375444570 : (((p2 ∨ p3) → (((False → (p5 ∨ True)) ∧ ((p2 → (p4 ∧ p4)) → p1)) ∨ p3)) ∨ ((False → p5) ∨ (((p5 ∧ p3) ∧ (p3 → True)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256275284582374015552746472243 : ((False ∨ p1) → (((((p5 → (False ∧ (p4 → True))) ∨ True) ∨ p5) → (p2 → ((False ∨ (((False ∧ p3) → False) → (p5 ∨ False))) → p3))) ∨ True)) := by
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
theorem thm_5_vars_20909154034173939313652738481 : (((False ∧ (((True ∨ p1) ∨ p4) ∧ (((p2 ∨ p2) ∨ p3) ∧ p4))) ∨ ((p2 → (True → p4)) ∨ (((p1 ∧ p4) → True) ∨ (p4 ∧ p5)))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330835781520709237820282947660 : (True → (p3 → (((((((((p3 → ((p4 ∧ (True ∨ p3)) ∨ p5)) ∨ True) ∨ (p5 ∨ p5)) → (p1 ∨ True)) ∧ p2) → p2) → False) ∨ p3) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664286029426463103759763383251 : ((((p2 ∨ ((((p3 → (p3 → ((p2 ∨ ((False ∨ p1) ∨ p3)) → p3))) → (p4 ∧ (False ∨ (p3 ∨ True)))) ∧ p1) ∧ p1)) → (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168301833524593820559792683602 : (((p2 ∨ p3) ∧ ((p2 → p3) ∧ (p5 ∨ ((((p4 → p4) ∨ True) → (True ∧ p3)) → p4)))) → (((((p3 ∨ p4) → p5) → p3) ∨ False) ∧ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251165929186379451195228398590 : ((p2 → p1) ∨ (((((((p2 → ((p2 ∧ p4) → ((p1 ∧ (p1 ∧ p5)) ∧ (False ∧ p2)))) ∨ False) → (p5 ∨ False)) → False) ∧ p5) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_171503651689160801848708325222 : ((((((p4 ∧ p5) ∨ (((p1 ∧ True) ∨ p2) ∧ (p1 → p3))) ∧ p4) ∧ p2) ∨ True) ∨ (((((p3 → p4) ∨ p5) ∨ p1) ∨ True) ∨ (False ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308390134173021114664946343426 : (p2 ∨ (((((p2 ∧ p5) ∨ p3) ∧ ((False ∧ p2) ∨ ((False → (p5 → ((True ∨ p5) → p4))) ∧ (((False ∨ p3) ∨ p3) ∨ p1)))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111232527467315839875057006432 : ((((p5 ∧ p3) ∧ (p4 ∧ ((((((p3 ∧ (p1 → p4)) ∨ p3) ∧ (((False ∨ False) → p2) → p4)) ∧ p5) ∧ p3) ∨ p1))) ∧ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356879587876430075903309337663 : (p5 → ((p4 → ((p4 → True) → p2)) ∨ (((p5 ∨ p4) → ((p2 ∧ (((p3 ∨ p3) ∧ p1) → (p4 ∧ (p4 ∧ p2)))) ∨ (p5 → True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301268170578049282883203027366 : (False ∨ ((p4 ∨ ((True ∧ p2) → (p1 → p5))) ∨ ((((p3 ∨ False) ∧ p1) ∧ p5) → ((p1 ∧ (p3 ∧ ((p1 → True) → False))) ∨ (p3 ∨ False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665686125296131343420546290999 : (((((p5 ∧ (p3 ∨ ((p2 → ((((((p1 ∧ p4) ∧ p1) ∨ False) ∨ (p3 ∧ p5)) ∧ p2) ∨ p2)) ∧ True))) ∨ p3) ∧ ((False ∧ p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166102961981984021353681593253 : (((p2 → p3) → ((((p2 ∨ p5) ∨ p2) ∧ (p2 → p4)) ∨ (p1 → (p5 ∨ (False → p2))))) ∨ (p1 ∧ ((p2 → (True → (p2 ∧ p5))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594344732720643488732733821250 : (((((((p1 ∧ True) ∧ ((p2 → p5) ∧ (p5 ∨ p3))) → ((p2 ∧ (True → p5)) ∧ p3)) ∧ (p3 ∧ ((p1 ∨ (False ∧ p2)) ∨ False))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669043998015192974549957381016 : ((((((((p2 ∧ ((p1 ∧ p5) ∧ (p2 ∧ ((True ∨ (p4 ∧ p5)) ∧ (False ∨ p4))))) → False) ∧ p5) → p5) → False) ∨ (False → (True ∧ p1))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146950896051668398079213363560 : (((((p1 → (p3 ∧ p5)) ∨ (p4 ∨ (p3 → ((p2 ∧ p5) ∧ ((p1 ∧ p5) ∧ (p1 ∧ p5)))))) ∨ True) ∧ True) ∨ (((p4 → p2) ∨ p4) ∨ p5)) := by
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
theorem thm_5_vars_691490576197384081972495093011 : (((((True ∨ p1) → ((p2 ∧ ((False → (p5 → (p2 ∧ (p2 ∧ p2)))) ∨ p4)) ∧ False)) → ((p3 → ((p2 ∨ p1) → (p3 → p5))) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47128123340729796468521079851 : (((((((p3 → True) → (p4 ∧ p2)) → p2) → (p2 → (p1 → (((p2 ∨ False) ∧ False) ∧ p2)))) → ((p4 ∧ True) ∨ p1)) ∨ (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87437298755074235334177903837 : (((True → (((p2 ∧ p2) ∧ p4) ∧ False)) ∧ ((p5 ∨ p5) ∧ (((p4 → p4) ∨ p1) → (((p1 → p2) ∧ (p3 → (p1 ∧ False))) → p1)))) → p2) := by
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
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52819035921447629106493343557 : (((((p4 ∧ (p3 ∧ p1)) → True) ∨ (((p3 → (p2 ∧ p5)) → p2) ∨ p2)) → (p3 ∧ (p5 → (p2 ∨ ((True ∨ (p1 ∨ p1)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138858415396508393196273560814 : (((p1 ∨ ((((p3 ∧ (p4 → ((((False → False) → p2) ∨ p3) → ((True ∨ p2) ∨ p4)))) ∨ p3) → p3) ∨ p1)) ∧ p1) → ((p4 ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_161518493479097364269981539203 : ((p4 ∧ (False ∨ (((((p5 → (((p1 → True) → False) ∧ False)) → p5) ∨ (p3 ∧ p5)) ∨ p4) ∧ p5))) → ((p3 → p1) ∨ (True ∨ (True → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651880029079529597615412881940 : (((((p4 ∨ p2) → (((p4 ∧ (False → ((p5 ∨ p1) ∧ p4))) → (p1 ∧ p1)) ∨ ((p3 ∧ (p4 ∨ p3)) → (p3 → True)))) ∧ (True ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113827696581422596783964673034 : (((True ∨ (((((p5 ∧ p5) ∨ p4) ∨ p3) ∨ (((True → p4) ∨ p3) ∧ True)) ∧ (False → ((False → p1) ∨ p3)))) → (p1 ∧ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207733697937501122748683520483 : (((p4 ∧ (p1 ∧ (p3 ∨ False))) → p1) → ((p4 → ((p2 ∧ (p5 ∨ (((True ∨ p5) ∧ ((p1 → p1) ∧ p1)) → (p2 → False)))) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193087846313098862181533886367 : ((((p4 ∨ p5) → (p1 → p3)) ∧ ((p1 → p2) ∨ False)) → (((True → (((p3 → p3) ∧ p1) → p5)) ∨ (p1 ∨ p1)) ∨ ((p1 ∧ False) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131626375272543315003129597324 : (((p4 ∧ (p1 ∨ False)) ∨ ((((False ∨ p3) ∧ (p4 → False)) ∨ p1) ∨ (p1 → (True ∨ (False ∧ (p5 ∧ (p3 → p3))))))) ∧ (p3 ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59914866639190808395137483412 : (((p5 ∧ p3) → ((((False ∧ p5) ∨ False) ∨ (True ∧ (True ∧ (p3 ∧ p1)))) ∨ (False ∨ ((p4 ∨ p4) ∧ ((p4 ∨ p5) ∨ (p5 ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313012291416719550812504112967 : (p3 ∨ (((((True ∧ (p3 ∧ p5)) ∨ p2) ∨ (((((p2 ∧ False) ∧ (p5 ∧ p5)) ∨ (p5 ∨ True)) ∨ p5) ∨ ((False ∧ False) → p5))) ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204846936012169569643946116833 : (((((p3 ∨ p4) ∧ p1) → p3) → p3) ∨ ((((p2 ∧ (True ∨ True)) ∨ True) → p3) → (((False ∨ (False → p1)) → p2) → ((p3 ∨ p4) → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∧ (True ∨ True)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149149305878869135905115408000 : (((False ∨ p3) ∧ ((p4 ∨ ((p1 ∧ ((False → ((False ∧ p2) ∨ ((True ∧ p4) ∧ p1))) ∧ True)) ∧ p4)) ∧ True)) ∨ (False → ((p1 → p4) ∧ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16674966653122971571081357948 : ((((p2 ∧ ((False → ((False ∧ (False ∨ True)) ∧ (p4 ∧ p1))) ∧ ((p1 ∧ (p4 ∧ (p3 ∧ p5))) → p5))) → p4) ∨ (False → (p4 ∧ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38807241057972211638209580870 : ((((((False ∧ False) → False) ∨ p5) → (((p3 → (False → p1)) → ((((False ∨ (p5 → (p3 ∨ p5))) ∨ p2) → p2) ∨ p2)) ∨ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44038925201466867589614611866 : ((((p4 ∧ (((p5 → (p5 ∨ p2)) ∨ (p4 → (((p3 → ((p5 ∨ p4) → p5)) ∨ True) → (p3 ∨ True)))) ∧ True)) → (p3 ∨ True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338830191455361834154696521586 : (p1 → ((p5 ∨ p5) ∨ (((((((p5 ∨ True) ∧ (p5 ∨ True)) ∨ p3) → ((p3 ∨ p2) ∧ p4)) ∨ p5) ∧ p4) ∨ (p5 ∨ (True ∨ (p5 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_786184700631313673567084635827 : (((p4 ∨ ((((p5 → p2) ∨ (p4 ∧ (False ∨ (((p4 ∨ ((p4 ∧ (p5 → p4)) → p4)) ∧ p2) ∨ p2)))) ∨ True) → ((True → False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41961609097286795402147116029 : ((((p5 ∧ True) ∧ ((((p1 ∨ (p2 ∨ p3)) ∨ ((True ∨ (True ∨ (p1 → p2))) ∨ (p4 ∧ p2))) → (p3 ∧ False)) → (p3 ∨ p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341660471447404949842312363688 : (p2 → ((((p1 ∧ (((((True ∨ p1) → False) ∧ (False → (False ∧ ((True ∨ p3) ∧ p5)))) → False) ∨ p4)) ∨ (False → p3)) ∧ True) ∨ (p1 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190955702104206857842821267597 : (((False ∨ ((p4 → p3) → p2)) ∧ (False → (False → p4))) ∨ ((((p4 ∨ True) → p4) → (p4 ∨ ((p4 ∧ True) ∨ p2))) ∧ (p4 ∨ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158856016713939406143417706188 : ((False ∨ ((True → (((p3 ∨ p4) ∧ (((p2 ∨ (True ∨ (False → p3))) ∨ p2) ∨ True)) ∨ False)) ∧ p4)) ∨ (((True ∨ p2) → p4) → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625172793777423356471482897085 : ((((True → ((((p1 → True) ∨ True) → p2) ∧ (((False ∧ p5) ∧ ((p3 → ((((True ∨ p2) ∧ False) ∨ p1) ∧ p3)) → False)) ∧ p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_184431992315264968345584126669 : ((((p4 ∨ (p3 ∨ p4)) ∨ (True ∧ (p1 ∧ True))) ∧ (p3 ∨ True)) ∨ (False → (p5 ∧ (((True ∧ p1) ∧ p5) ∧ (True ∧ (p3 ∨ (p3 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41875109769061912084808342420 : ((((False ∧ (False ∧ p5)) ∨ ((((False → True) ∨ p2) ∧ p5) → ((p5 ∧ ((p4 → True) → p2)) → ((p3 ∨ p1) ∧ (False ∧ p4))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116841858628892782027676960543 : (((True → p3) ∨ ((True → ((p1 → (p3 ∨ p4)) ∨ p2)) ∧ ((((p4 ∨ ((p5 → False) → p1)) → p4) ∨ (False → p4)) ∨ p2))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51244691062334993024655780729 : (((((p1 ∨ p3) ∨ p1) → (True → ((((((p2 ∨ False) ∨ p4) ∧ p5) ∨ p1) ∨ p2) ∨ True))) ∨ (p1 ∨ (p5 → ((True ∨ p1) → True)))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111665634372156973765421901852 : ((((p2 ∨ (((p4 ∧ (p3 → ((p2 ∨ False) ∧ p1))) → ((((True ∧ p1) → p3) ∨ p5) ∨ p4)) ∧ (False ∧ p2))) ∨ p4) ∨ p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164944782842539255623555175374 : ((((((((p4 ∧ p3) → p2) ∨ ((p1 ∧ p5) ∨ True)) ∨ (p1 ∧ p4)) → p1) → False) → p5) ∨ ((p2 ∧ (False → True)) → (p2 ∨ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1767442381059358047325152013 : ((((p2 ∧ p1) ∧ ((p3 ∨ (((True → ((p3 ∧ (p1 ∨ (True ∨ p1))) → p5)) ∧ p2) → False)) ∧ p1)) ∨ p1) ∨ (True ∧ (p1 → p1))) := by
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
theorem thm_5_vars_159523303480860557742848322332 : ((((p2 → p2) → ((p3 → (((p1 ∧ ((p1 ∧ p5) ∨ p1)) ∨ (p3 ∨ False)) ∨ p4)) → p2)) ∧ p1) → (p2 ∨ (p1 → (p2 ∧ (True ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → (((p1 ∧ ((p1 ∧ p5) ∨ p1)) ∨ (p3 ∨ False)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693150909201147415314521940967 : ((((p5 ∧ (((True ∨ p4) ∨ (p3 ∨ ((p1 ∨ p2) ∨ True))) ∧ (True ∨ p3))) ∧ ((True ∧ (((p1 → (p1 → False)) ∨ p3) ∨ False)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115480085025923029328338959719 : (((p4 → (((True ∧ p4) ∧ (p4 ∧ p5)) ∧ p2)) ∨ ((((True → ((p2 → p2) ∧ (p1 ∨ False))) ∨ (p5 ∧ p1)) ∨ p5) → p4)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640598758781470984497918728610 : (((((False ∨ p5) ∧ ((((p5 → (p1 ∧ True)) ∨ (p4 ∨ p1)) ∨ ((p3 ∨ (p5 → p3)) ∧ p3)) ∧ (p1 ∧ (False ∨ (p4 → p3))))) → p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h7.left
          let h17 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h7.left
          let h22 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h21
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h7.left
        let h30 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h7.left
        let h35 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- One of the premise coincides with the conclusion.
          exact h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712050666950390608264670759149 : ((((((p3 ∧ p3) → (p2 ∧ p1)) ∨ p5) ∨ (((((False → True) → ((p2 → (False → True)) ∧ (p2 ∧ p2))) ∨ p5) ∨ (p5 → p4)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_182986020354103447225897086648 : (((False → p1) ∧ (((True ∨ (p2 ∧ p5)) ∨ (p2 ∨ p3)) ∨ p4)) ∧ (p5 ∨ ((((p4 ∧ p5) → p4) → False) ∨ (True ∧ (p2 ∨ (False ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212285136629974204755706324247 : ((p1 ∨ ((True ∧ True) ∨ False)) ∧ ((((p3 ∨ False) → (((p5 ∨ p3) ∧ p2) ∨ ((p4 ∨ ((p4 ∨ True) → True)) ∨ p3))) ∧ (p5 ∨ True)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41452286113007804435314777808 : ((((((p2 ∨ p5) → (False ∧ ((p1 ∧ p4) ∧ (True → True)))) → p2) ∧ (((True ∨ (p2 → (p2 → p5))) ∨ p3) → (p4 → p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219487222898279567988464532584 : ((p5 ∨ ((p1 ∨ p5) ∧ True)) → ((p3 ∨ p3) → ((True ∧ (((p2 ∧ (p1 ∨ ((True ∨ (True ∨ p5)) ∧ p3))) ∧ p1) ∧ p3)) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57239551297790537999401403220 : ((((p1 ∧ p5) → p3) ∨ ((p3 → True) → ((False ∨ (p3 ∧ ((True ∧ p1) → (((p5 ∨ (p4 ∧ (True → p1))) ∧ p3) ∨ False)))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178351091464021364764066173365 : (((p5 ∧ ((p2 ∧ (p1 ∨ p1)) ∨ (p3 → (p1 → p5)))) ∨ (p4 ∨ False)) ∨ (((False ∧ p4) → p3) → (True ∧ (False → (p5 ∨ (p2 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80334199681996827615707345710 : (((((((((p2 ∧ (p5 ∧ True)) ∨ (p4 ∨ p4)) ∨ False) ∧ p4) → p1) → (p1 ∨ False)) ∨ ((p5 ∧ (p4 → p4)) → True)) → (p2 ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p2 ∧ (p5 ∧ True)) ∨ (p4 ∨ p4)) ∨ False) ∧ p4) → p1) → (p1 ∨ False)) ∨ ((p5 ∧ (p4 → p4)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156823922050424981605969210686 : (((p4 ∨ (True → ((p5 ∨ (p1 → (p4 ∧ (p3 ∨ (True ∧ True))))) ∨ ((p5 ∨ p2) → True)))) ∧ p3) ∨ (True ∨ (((p5 ∨ p5) ∧ p4) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655869331028169832637742001687 : ((((((p2 ∧ p1) ∧ ((True ∧ p3) → (((True ∨ (p4 ∧ p3)) → (p5 ∧ (p3 ∨ True))) → p1))) → (False ∧ (p1 ∧ p3))) ∨ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550538613656563756429023733264 : (((p1 ∨ ((p2 ∧ ((p5 → (True ∧ (p2 → (p2 ∧ (p4 ∨ False))))) ∨ ((((p3 → p3) ∨ p2) → p2) ∨ (True → p4)))) ∨ (False → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657212703597302206013026827390 : ((((((True ∧ p5) → p5) → (((True ∧ ((((p1 → p1) ∨ ((p3 → p4) ∧ p2)) ∧ p4) ∧ p3)) ∧ p1) ∧ (True → p3))) ∨ (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165216202976922109469677533292 : ((((p3 ∧ ((p4 → p2) ∧ ((True ∨ False) ∨ p1))) ∧ (p2 ∧ (p4 ∧ p5))) ∨ (False ∧ p5)) ∨ (True ∨ ((p4 ∨ p2) ∧ ((True → p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38105106815491304904815142209 : ((((((p1 ∨ (p2 ∧ ((p2 ∨ ((p1 ∨ p5) ∨ ((p1 ∧ (p2 ∧ p4)) → False))) ∨ p4))) → True) ∧ p3) ∧ ((False ∧ p1) ∧ p3)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716410568111105532695037141302 : (((((p1 → p1) ∧ (False ∨ True)) ∧ (((p4 → (True ∨ ((False → (p4 ∨ p1)) → p1))) → ((p1 → True) ∨ p5)) → ((True → False) → p4))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219993008405271578906992097934 : ((p5 → (p1 ∨ (p3 ∨ False))) → (((False ∧ (((p1 ∧ p3) ∨ p4) → p1)) ∨ (p5 ∧ (((True ∧ True) → False) → (p5 → (p4 → p3))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47545289400064986687571231209 : (((p5 ∨ ((p3 ∧ p1) ∧ ((p3 ∧ (((((((p3 → False) → p2) ∨ (p3 ∨ p4)) → True) ∨ True) → True) → p5)) ∨ False))) ∨ (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252450675958833132556715681525 : ((p5 → p1) ∨ ((p2 ∧ (False ∨ (False ∧ (True → (((False ∧ ((p1 ∨ p4) ∨ True)) ∧ ((p2 ∨ ((p1 → False) ∨ True)) → p5)) ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64053116594577060983613185766 : ((False ∨ (((p2 ∨ (p5 → (True ∧ True))) ∧ (((p5 ∨ p5) ∧ ((True ∧ p4) ∨ p3)) ∧ (p1 ∧ p4))) ∧ ((p3 → (False ∧ p5)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135184768884492450178492699837 : ((((p3 → ((p5 ∨ ((p3 → ((p3 → p2) ∨ p2)) ∧ p3)) ∨ (((p5 ∨ p5) ∧ p2) ∨ p1))) ∨ p3) → (p5 ∧ True)) ∨ (False → (p5 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355534283863283803932784840332 : (p5 → (((p1 ∧ ((p1 ∧ p3) ∨ ((p4 ∨ (p3 ∧ ((p1 ∨ p1) ∨ (True ∧ p1)))) ∧ ((p2 ∨ (p1 ∧ False)) ∧ p2)))) ∧ p4) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768672865034379103528340292220 : (((p5 ∧ ((((False ∧ False) ∧ ((False ∧ p5) ∨ p5)) ∧ (p5 ∨ p4)) ∧ ((p4 ∨ (p2 ∧ (p5 → ((p2 → (p1 → p4)) → p4)))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43390929479499127069217079658 : ((((((p2 ∨ ((p5 → (((((p5 → p5) → p5) ∧ p4) ∧ p2) ∧ True)) ∨ p4)) ∨ False) → (True ∧ ((p1 ∧ True) ∧ p5))) ∨ p2) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320335618867458840843748182132 : (p4 ∨ ((p5 ∨ p2) ∨ ((((p5 ∨ ((((True ∧ p3) → (p3 → p4)) ∨ True) ∨ p1)) → p5) → p3) ∨ ((True ∨ False) → (True ∨ (p2 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803831712153966964821843003059 : (((p3 → (((((p4 → p2) ∨ p4) → (p5 ∨ True)) ∧ (p2 → (p3 ∧ ((False ∧ (((p1 → True) ∨ True) ∨ p5)) ∧ p1)))) ∨ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219534801795108661989285356242 : ((p5 ∨ (p4 ∨ (p2 ∨ p3))) → (p4 ∨ ((p1 ∨ p1) ∨ ((p5 → (p1 → p1)) ∨ ((((p3 ∨ p5) ∨ p5) ∨ (p1 ∧ p1)) ∧ (p2 ∨ p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313949709362960953776689344506 : (p3 ∨ (((False ∨ ((((False ∧ False) ∨ (((p1 ∧ (p5 ∧ (p3 ∧ (p3 ∧ p1)))) → False) → (p3 ∧ False))) ∨ False) ∨ True)) → False) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330564131526341984005817264651 : (True → (p5 ∨ (((((False ∧ p3) → p3) ∨ (p4 ∧ p2)) ∨ p3) → (((p5 ∨ (p5 → (p5 → (False → p4)))) ∧ p4) ∨ ((p5 ∨ True) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165160417405202861039093833977 : (((((False ∧ False) ∨ p5) ∨ (((p5 → p5) → p5) ∨ (False → (p1 ∧ p5)))) ∧ (p5 ∨ False)) ∨ ((((p2 ∧ p3) ∨ False) ∧ p4) → (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230352397669665289390728678049 : (((p2 ∨ p4) ∧ True) → ((p5 ∨ (p5 ∨ (False → (p3 → (p5 → True))))) ∧ ((p2 → (True → (False ∨ (((p1 → p1) ∧ p5) ∨ p5)))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208614437205182410209154681876 : (((p5 → p5) → (p3 ∧ (p1 ∨ p3))) → (((((p1 → p3) → ((p2 ∧ ((True → p4) ∨ False)) ∧ ((p5 ∨ p1) → True))) ∨ p4) ∨ p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253856958661997695842445158272 : ((p1 ∧ p3) → (((p5 ∧ p2) ∧ (((p1 ∧ (False ∨ (p2 ∧ (p1 ∧ (p2 ∧ (True → p1)))))) → (p4 → (False → False))) → False)) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328538073685973380715938692499 : (True → ((p2 → (p2 → (((True ∧ False) ∧ ((p3 ∨ p5) ∨ (p2 ∧ (p1 ∧ p1)))) ∧ p1))) ∨ ((p1 → True) → (((p3 ∧ p2) ∧ p4) ∨ True)))) := by
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
theorem thm_5_vars_142513120603317510451508780578 : ((True ∨ (((p5 ∧ (p3 ∧ (p2 ∨ p2))) ∨ ((p5 ∧ p3) ∨ (((p4 → False) ∧ p4) → ((p5 ∧ p5) → p5)))) ∨ p1)) → (p4 ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187571176662059178807769328157 : ((p3 ∨ ((((p5 ∨ p4) ∨ False) ∧ (p5 → (p3 ∨ p1))) → True)) → ((p3 → p5) ∨ (((p3 ∨ (False → p4)) ∧ True) ∨ (False ∨ (p1 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318646524230632751869437576753 : (p4 ∨ ((p4 ∨ ((False ∧ True) ∧ (((((p1 → p2) → p1) → p2) ∨ p1) ∧ (p1 ∧ (p2 ∧ (p3 ∧ (False ∨ (p4 → p3)))))))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



