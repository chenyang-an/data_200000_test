variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330902297019891790563867209440 : (True → (p4 → ((((p5 ∨ (((p2 ∧ p4) ∧ (p1 → True)) ∨ p2)) ∨ ((True → (True ∧ p5)) → ((p1 ∧ p5) → (p2 → p3)))) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184385989110536718794064217886 : (((p2 → ((((p5 ∨ p1) → (p1 ∧ False)) ∨ p5) → p1)) → p3) ∨ ((p1 ∨ False) ∨ ((p3 ∧ ((p2 ∧ p4) ∧ p1)) → ((p5 ∨ True) ∨ p2)))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245545730723687571283867864764 : ((p3 ∧ True) ∨ ((((p3 → p3) ∧ (False ∧ (((True ∧ True) ∨ (p4 ∨ p2)) ∧ p3))) ∧ p5) ∨ ((p4 ∨ p1) ∨ (((p5 ∧ p4) → p5) ∨ p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323219193272312594199060951793 : (p5 ∨ (((p3 ∧ (((((p3 ∨ True) ∨ True) ∨ (p5 ∨ p2)) ∨ True) ∨ (p5 ∨ False))) → (((p5 → (False ∧ p3)) → p1) ∨ p3)) ∨ (p5 ∨ p1))) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
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
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785937723246742829023586538129 : (((p4 ∨ (((((p4 → ((((p4 → (False → p2)) ∨ p2) → (p4 → p2)) → (False → (p2 → p1)))) ∨ p4) → False) ∧ p5) ∨ (p3 → p3))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107428612702088493759447595483 : ((((False → p1) ∨ p1) → ((((p4 → (False ∨ (False ∨ (True → p2)))) ∨ (((p5 ∧ p5) → True) ∨ p3)) ∨ p1) ∨ (p3 ∧ p1))) ∧ (False → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133542968313567913378673076905 : ((((p2 ∧ ((((((p5 → False) ∧ (p4 ∧ (p2 → p5))) ∨ p3) → (True → False)) ∨ (False ∧ p4)) ∨ p1)) ∧ p4) ∧ p3) ∨ ((False → False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262232092191747427366137952998 : (True ∧ ((((p5 → (p5 → (p1 ∨ p3))) ∧ (((True ∨ True) ∧ p1) → (True → ((p3 → p3) → ((p4 → p3) ∨ p2))))) ∨ (p3 ∨ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165474036625143268571015419103 : ((((((p4 → p4) → (p5 ∨ (p1 ∨ p5))) ∧ p1) ∧ True) ∨ ((p1 → (p1 ∧ False)) → p4)) ∨ (p4 → ((False ∨ p2) → (False → (p5 ∧ p3))))) := by
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
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729107747791029871376084700623 : (((((True → p5) ∧ p1) → ((((((p1 → p3) ∨ ((p5 ∨ True) ∨ p1)) → ((p3 ∨ p3) ∨ (True ∨ True))) ∧ (p4 → p2)) ∨ p1) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147463805489783504552089865014 : (((True ∧ ((((p2 ∧ p4) ∨ p3) ∧ (p5 ∨ p3)) ∨ ((False ∨ True) ∧ (True ∨ ((p5 → p3) ∧ True))))) ∨ p4) ∨ (p3 ∨ (p2 → (p2 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114111816126736621413977603819 : (((p1 ∨ (p3 ∨ (p2 ∧ (((p2 → ((p2 ∧ ((p5 ∧ p4) ∧ (p2 ∧ p3))) ∧ True)) ∧ p5) → p3)))) ∨ ((True ∨ p5) ∧ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111904289012157360153516896088 : ((((p3 ∧ (p2 ∨ (((p1 ∧ (p3 ∨ (p4 ∨ (p5 ∧ p2)))) → p2) → p3))) → (((p3 ∧ True) ∧ p1) → (p5 ∨ p2))) ∨ False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199530499367753273689244127469 : (((((p5 ∨ (p5 ∨ True)) ∨ True) ∧ p5) → p1) → (p5 → ((p4 → False) → ((p1 → (p5 ∧ (((False ∨ p2) ∧ (p3 ∧ False)) ∧ p2))) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (((p5 ∨ (p5 ∨ True)) ∨ True) ∧ p5) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743546062910214091855209843877 : ((((True ∧ True) → (((p4 ∨ (p1 → ((p5 ∧ (False ∧ ((False ∨ (p3 → p4)) → p5))) ∧ (p5 ∨ p4)))) → (p4 ∧ (False ∧ p5))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612512938835921918497188136756 : (((((((((p5 ∨ p3) → ((p4 ∨ p3) → ((p3 ∨ (p5 ∧ p4)) → p3))) → p1) → (p1 → (False ∧ p1))) ∨ p2) ∨ (p3 → p2)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599485810100085433400472442293 : (((((p1 ∨ False) ∨ ((((((p4 ∧ p5) ∧ p3) ∨ p5) → p4) ∧ (p3 ∨ False)) ∧ (((p5 ∧ False) → (p4 ∨ p3)) → (p4 ∨ True)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169100220050801823568945611598 : ((p4 → ((((((True ∧ True) ∧ p2) ∨ p5) → p3) ∧ p3) → ((False ∧ p5) ∨ (False → False)))) → ((p1 ∧ ((p3 ∨ p4) ∧ (p2 ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148585962926721714087801780902 : ((((((p3 ∧ (p1 ∨ False)) ∨ False) ∧ p5) ∨ (True → p2)) ∨ (False ∧ ((((True ∨ p5) ∧ p1) → p4) ∨ p1))) ∨ (True ∨ (p4 → (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53844142900837099791829614783 : (((((p2 → (p4 → p5)) ∧ p5) → (p4 ∨ (p4 ∨ p1))) ∨ ((p4 → (p3 ∨ p5)) → (False → ((p2 ∧ (p2 ∨ False)) → (p4 ∧ p2))))) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15034145114417698369486308958 : (((True ∧ ((((True → p1) ∨ ((True ∧ p5) ∧ p4)) ∧ ((False ∨ (p1 ∨ ((p5 → False) → (False ∧ p4)))) ∧ p4)) ∧ p2)) ∨ (p1 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_670378007373592021866803355684 : (((((p5 ∨ (p2 ∨ p2)) ∨ ((((p5 ∧ p2) ∨ (((p5 ∧ p3) → (p2 ∧ (p2 ∧ p2))) → False)) ∧ p5) → False)) ∨ (True ∨ (p4 ∧ p1))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_66819007379825117210908183902 : ((True → (True → (((p4 ∨ ((p5 ∧ p4) → ((p3 ∧ p2) ∨ (((False ∧ p1) ∧ (False ∧ True)) ∧ (True ∧ p5))))) → p3) ∨ (p2 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51881387065325089409336028804 : (((((p3 ∨ ((p1 ∧ (False → (p5 ∨ (p1 → False)))) ∨ (p2 ∨ False))) ∧ p4) → p1) ∨ ((True ∧ (False ∧ (p5 ∨ False))) ∨ (False → p2))) ∨ p1) := by
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
theorem thm_5_vars_186130996079106151921132882570 : (((((True ∨ p5) ∧ p1) ∧ (((p1 → p3) ∧ p4) ∧ p1)) ∨ p4) → (((p4 → p2) ∨ False) ∨ (True ∨ ((True ∧ p3) ∧ ((False → p1) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h4.left
      let h9 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634492762946575923860336836837 : ((((((p5 ∧ (((p5 ∧ p4) → p1) ∨ ((p3 ∧ p1) → p2))) ∧ ((p2 ∨ (p4 ∨ (True ∨ p2))) → p5)) ∧ (p2 ∧ (p3 ∧ p5))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158421611225611284029785185894 : (((p4 ∧ p1) ∨ (((p2 → p5) ∨ (p2 ∧ p4)) ∨ (p2 ∨ ((False → p5) ∧ ((p4 ∧ p3) ∧ p3))))) ∨ (((p3 ∨ (False ∧ p2)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165802350469854198844897721284 : ((((False ∨ p4) ∨ True) ∧ (False ∨ ((p2 → False) ∧ (True ∧ (p4 → ((p5 ∧ True) ∨ False)))))) ∨ ((True → False) → ((p1 ∧ (True → p3)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50036422770815973092228866469 : ((((p3 ∨ (p3 ∨ p5)) ∧ (((p2 → True) ∨ (True ∨ (((p5 ∨ p3) → p2) ∧ p4))) → (p5 ∧ p4))) ∧ ((False ∨ (p4 → p2)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205470522421912469983910922901 : (((p4 → (p2 ∨ p4)) → (p3 ∨ p2)) ∨ (p3 ∨ (p2 → (((((((p4 ∨ False) → True) ∨ False) ∨ p4) ∨ (p5 ∨ (p4 ∧ p3))) → False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p4 ∨ False) → True) ∨ False) ∨ p4) ∨ (p5 ∨ (p4 ∧ p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248998961178911038672227565330 : ((p4 ∨ False) ∨ ((p4 ∨ ((((p4 ∨ (p3 ∧ (p3 ∧ True))) → (p2 ∨ p3)) ∨ (p3 → False)) ∧ ((False ∨ (p3 ∨ True)) ∧ p2))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610449830910185002137142118433 : (((((((p2 ∨ p5) ∧ ((False ∨ (p5 ∧ ((((p4 ∧ False) ∨ False) ∨ (p2 ∨ False)) → False))) → (p4 ∨ (p5 ∧ False)))) → True) → p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_200542511768941700632171929958 : (((True → p5) → ((p3 → p2) → (p3 ∧ p2))) → ((((p5 ∧ ((True → True) ∨ (p4 ∨ False))) → (False ∨ p3)) → (p3 → p1)) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144712428613620607213665706284 : ((((((p2 → (p3 → p1)) ∨ (p3 ∨ (p2 ∧ p5))) ∨ p2) ∨ (p4 → (False ∨ True))) ∧ ((p5 ∨ True) ∨ False)) ∧ ((p4 ∨ (False ∨ True)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198215447644448095167501932900 : ((True ∧ ((((p2 ∧ True) ∨ False) ∨ False) ∧ p2)) ∨ (p1 → (p4 ∨ (p5 → (((((p1 → p2) ∨ p2) ∨ p1) → (True ∨ (False ∧ p3))) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730554857079294796355855115158 : ((((p1 ∧ (False → False)) → ((((p5 → (True ∧ True)) ∨ (False ∧ (p3 ∧ p3))) → (p3 ∨ (p4 ∨ p3))) ∨ (p1 ∨ (p5 ∨ (p4 ∨ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184500331533263398694779920350 : ((((True ∧ (p2 ∨ p3)) → ((p3 → False) → p4)) ∨ (p2 ∨ p2)) ∨ ((((p2 ∧ (p4 ∨ (p5 → (p5 ∨ True)))) → p3) ∨ (p1 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648718573006360151523574021473 : (((((p1 ∧ ((((((True → (p5 ∨ p4)) ∧ p5) ∧ (True ∨ p2)) ∨ (False ∨ (p3 → (p1 ∧ p1)))) ∨ p3) ∨ False)) ∨ p2) ∧ (p2 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729348236050940940001440932647 : (((((p2 ∧ False) ∨ p4) → ((p1 ∨ (((p2 → (False ∨ p3)) → (((False → False) → ((p5 ∨ p2) ∨ p5)) → p3)) ∧ p3)) ∨ (False → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259479275860384361953572919174 : ((False → p4) → (p5 ∨ ((p4 → (p1 → ((((p1 → p5) ∨ True) ∨ p3) ∧ (False → (p2 ∧ (True ∧ p5)))))) ∨ ((p3 ∨ p4) ∨ (p5 ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185158737523429592506128902353 : (((p4 ∨ p3) → ((((False ∨ p1) ∨ (p3 ∧ p5)) → False) ∧ p5)) ∨ (p4 → (p2 ∨ ((((p3 ∧ p4) → (p1 ∨ True)) → p3) → (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_40417228292416616127099215654 : (((((p3 ∨ ((((p3 ∧ p5) ∨ (p3 → (p3 ∨ (True → False)))) ∧ p1) ∧ (p4 → p3))) → (((p4 → p3) → False) ∨ p1)) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206853387502925458213956256313 : (((((p5 ∨ p1) ∧ p5) ∧ p4) ∧ True) → (((p2 ∨ ((False ∧ (False ∧ p3)) ∨ (p4 ∨ ((p1 ∨ p1) ∨ False)))) ∨ False) ∨ (False → (p2 ∨ p2)))) := by
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
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782501034677494061418978733027 : (((p3 ∨ ((((False → p4) ∧ p5) ∨ (p4 ∨ ((True ∧ (p3 ∧ (p1 ∧ (p4 ∧ (True → (p4 ∨ (p1 ∧ p4))))))) ∨ (p4 → True)))) ∨ p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_197976157836465780300634723905 : (((p1 ∨ p1) ∧ (p2 ∧ ((p4 → False) → p1))) ∨ (p1 ∨ (p1 → (p5 → (((False ∨ (False ∧ ((p2 ∨ (p2 ∧ p3)) ∨ p3))) ∧ p5) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3220192559343996864842691784 : ((False ∨ p1) ∨ (((p1 → p2) ∧ p3) → ((False ∧ ((p3 ∧ (False → True)) ∧ ((p5 ∨ p3) → p2))) ∨ ((True ∧ p5) ∨ (False → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586435697320993121016795593990 : (((((((False ∨ False) ∧ p5) ∧ (((p3 ∧ True) ∨ p3) → (((p4 ∧ (((True ∧ False) ∨ (p2 → p3)) → p1)) ∧ p4) ∨ False))) ∧ True) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112328822851523397811314072426 : (((p4 → ((p1 ∧ (p3 → (p2 ∨ ((p1 → p3) ∧ (False ∨ ((p3 ∧ (p1 ∨ ((p5 → p4) ∧ p1))) ∧ p3)))))) ∨ p5)) ∨ p2) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775641741934370620791638649297 : (((False ∨ (p1 ∨ (((True ∨ (p4 → ((((True ∨ p3) ∨ (p2 ∧ p1)) ∧ p5) ∨ (True → p2)))) ∧ (((p3 ∨ p1) ∨ p2) ∨ p5)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266223866912357329581854401011 : (True ∧ (p4 → (False ∨ ((p1 ∧ (((((p2 ∨ (p4 → p3)) ∨ p2) ∨ (p2 ∨ False)) ∨ p4) ∧ p5)) ∨ ((p5 → ((p4 ∨ p5) → True)) ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113209938610495709283591446343 : (((((((p5 ∧ p3) → p1) ∨ p3) → (True → ((p5 ∧ p1) → (p4 ∧ ((p3 ∧ (True ∧ p5)) → p1))))) ∨ True) ∧ (p3 ∨ True)) ∨ (True ∧ p4)) := by
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
theorem thm_5_vars_709191472436457433343716878614 : (((((p1 ∨ p4) ∧ (((False ∧ p4) ∧ p2) ∨ p4)) → (((p1 ∨ (((p5 → p1) → p4) ∧ ((p4 ∨ p3) ∧ False))) ∧ (p5 ∧ p5)) ∨ True)) ∨ p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111907293084761870336547950251 : (((((p5 ∨ (((((False → False) ∧ p2) ∧ True) ∨ True) → p2)) ∨ p2) ∧ (((True ∧ p2) ∧ p1) ∧ ((p4 → p1) ∨ p2))) ∨ p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312031977589275445713409342466 : (p2 ∨ (p4 ∨ (p3 ∨ (p3 ∨ ((p2 ∨ ((((True → True) → ((p4 ∨ (p1 → p4)) ∨ p5)) → (True ∨ False)) ∧ (p4 → p3))) ∨ (p4 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754777623660344186194626220306 : (((False ∧ (False ∨ (((((p4 → (p5 → p5)) ∨ (p4 ∨ p5)) → p5) ∧ (((False ∧ False) → (p4 → p4)) → p1)) ∧ ((p5 → p1) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743032029289135727181206905837 : ((((p4 → False) ∨ ((p3 ∧ (((((p5 → ((False → (p2 ∨ p1)) ∨ p3)) ∨ p1) ∧ (p1 ∨ (True → p4))) ∧ (p4 ∨ p3)) → p1)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_111780849716671210377399093790 : ((((((((True → p2) ∨ p2) ∧ ((True ∧ False) → False)) ∨ (((p3 ∨ p5) ∧ p3) → (p4 ∨ p4))) → False) ∨ (p1 ∨ p1)) ∨ False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308708043027043678820396363835 : (p2 ∨ ((p5 ∨ ((((p5 ∨ p5) → (((p5 ∨ (p3 ∧ p1)) ∨ (False ∧ ((p2 ∨ False) → (p5 → True)))) ∧ p2)) → (p3 ∨ p5)) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343243458948178805389036534276 : (p2 → ((p4 ∨ (p1 ∨ p4)) → ((False ∧ ((((False ∨ p4) → ((p4 ∨ p5) ∨ (p4 → ((p1 ∧ p4) ∧ p1)))) ∧ p5) ∨ (p1 ∨ p5))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_112598841941541336364201067890 : ((((p1 ∨ ((((p3 ∧ True) ∧ True) ∧ ((True ∧ p4) ∧ (((True → True) ∧ p2) ∨ p2))) → (p2 ∧ p2))) ∧ (p5 ∨ False)) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337037249191573771826565741135 : (p1 → (((((((p3 ∨ (False ∨ p2)) ∨ p3) → (((False → True) ∧ (False → True)) → (p4 ∧ p1))) ∨ True) ∨ (p3 → p3)) ∧ p3) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63157906467703119949114208264 : ((p5 ∧ ((False ∨ (((p3 ∨ True) → p1) → (((p3 → (True → (True → p5))) ∨ True) ∨ (True → (p4 ∨ (p5 → p1)))))) ∧ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245402477770372923785199486805 : ((p2 ∧ p4) ∨ ((((p3 ∧ ((((p1 ∧ p3) → False) ∨ False) ∧ (p2 → p1))) ∨ ((p1 → True) ∨ ((p5 ∧ p4) → (p1 ∧ p1)))) ∨ p1) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181078810170622864637432847059 : (((p4 ∨ True) → ((True ∨ (((p2 → (p2 → p3)) ∧ p3) ∧ p4)) ∧ False)) → (((p5 → ((p3 ∧ p5) ∨ p5)) ∨ (True → p2)) → (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178779717567823868186578417974 : (((p3 ∨ (p2 ∨ True)) ∧ (p3 → (((p4 ∨ (p5 → p4)) ∧ True) → p5))) ∨ ((True ∧ (True ∧ (((p4 ∨ p3) → True) ∧ (p2 → True)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262325631593178053545022193060 : (True ∧ ((((p5 ∧ (p4 ∨ (p1 ∨ (p1 ∨ p4)))) → p2) → ((p2 ∨ p1) → (True ∧ (((p2 ∨ ((p3 → p2) ∨ p1)) ∧ True) ∧ True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44951468870944768573078079764 : ((((p1 ∨ p5) ∧ ((((p5 ∧ p1) → (((False ∨ (p1 ∨ ((p2 ∨ (p3 → p5)) ∧ False))) ∧ False) ∨ p1)) → (p2 ∨ p2)) → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599942022934177548025273130923 : (((((p4 ∧ p5) → ((p1 → True) ∧ (p3 → (((p3 → ((p4 ∧ p2) ∨ ((p4 ∧ (p3 ∧ p4)) → p1))) → (p1 ∧ p2)) ∨ p3)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181275595764393996391514907420 : ((p4 ∧ (True ∨ (True ∧ ((p3 ∧ p1) ∨ ((p3 → (p3 → False)) ∧ p3))))) → ((False ∨ (True ∧ ((False → p2) ∧ (p1 ∨ False)))) ∨ (p1 ∨ p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43646944978519393619927246470 : (((((False → (True → ((((p1 ∨ (p4 ∧ p2)) → p5) ∨ (((True → p5) ∨ False) → (p2 ∧ p5))) ∨ p3))) → (False ∧ p4)) → p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157614261774528155925895296529 : (((((False ∧ ((p5 ∨ p3) ∨ (p3 ∧ (p4 ∨ p2)))) → (p5 → p1)) → p4) ∧ (p4 → (p3 ∧ p3))) ∨ (True ∨ (p1 → ((p1 → True) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231058977405126105953980734003 : (((True ∨ p3) ∨ p4) → ((((((p4 → p5) ∨ True) → (((p2 ∧ False) ∨ ((p4 ∧ ((True → True) ∨ p5)) ∨ False)) → p1)) ∨ p5) → p2) ∨ True)) := by
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
theorem thm_5_vars_730959918668555021467573971706 : ((((True ∨ (p5 → p2)) → (((((p1 ∧ False) → p5) ∧ ((p4 ∨ p1) → (False ∨ (p2 ∨ p4)))) → ((p1 ∧ (p3 → p3)) → True)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303777526901287536575331064736 : (p1 ∨ (((p2 ∨ (p4 ∧ (((((p3 ∧ ((((True ∨ p5) ∨ p5) ∧ p4) ∨ p5)) ∨ p3) → p5) ∧ p3) → (p1 ∧ (p2 ∨ p5))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661282649942723563123479144342 : (((((((False ∧ False) ∧ (p5 ∧ ((p1 → (p4 ∧ ((p2 ∧ ((p5 → True) → p5)) ∧ p2))) ∧ p3))) ∧ False) → (p1 ∨ True)) → (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134833492468826720778880299650 : (((p2 ∨ ((((p3 ∨ False) ∨ p1) ∨ (p4 ∨ p1)) → ((p1 ∧ p3) ∧ ((p4 ∧ (p4 ∨ True)) → (p3 ∧ p2))))) → p2) ∨ (True ∧ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597278311789526444866907477506 : (((((p1 ∧ ((p2 ∧ p1) ∧ p3)) ∧ (((((p5 ∨ p4) → False) → (p3 ∧ p5)) ∨ ((p2 → p3) ∧ False)) ∨ ((p2 ∨ p1) → p5))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244872434124384842333017313381 : ((p1 ∧ p2) ∨ ((((p5 ∨ (False → p1)) → ((p3 → p3) ∧ p1)) ∨ (p1 ∨ (p1 ∧ ((p1 ∧ False) ∨ (p4 ∧ False))))) ∨ (True ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744761440989385591598843402967 : ((((p3 ∧ p2) → (((p3 → ((p2 ∧ p5) → (((p4 ∨ (((False ∨ p4) ∨ (False ∨ p4)) → True)) → (p2 → p3)) ∧ p4))) ∧ p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718354883258102246753689111474 : ((((((p3 ∨ p3) ∨ False) → p4) ∨ (p1 ∨ ((p4 ∨ (p2 ∨ (p4 ∨ (((p3 → ((p5 ∨ p1) ∧ p5)) ∨ p4) → p5)))) → (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658137393211987550060429801431 : ((((p4 ∧ ((p3 ∨ (p3 → (((p4 ∧ (((p1 → (p4 ∨ (False ∧ p3))) ∨ p4) ∧ p3)) ∧ True) ∧ True))) ∧ (False ∨ p5))) ∨ (p2 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_585583943713290706511733451822 : (((((((p4 → True) ∧ (((p3 ∨ (p2 → ((((p5 → p3) → p2) ∨ (True → False)) → p3))) ∧ (False ∨ False)) ∨ True)) ∨ p5) ∧ p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609496759724569058713776041511 : (((((p1 ∧ (((True ∧ ((True ∨ (True ∨ p5)) ∧ (p2 ∨ False))) → p2) → ((p5 → ((p3 → False) → (p2 ∧ p1))) ∧ p1))) ∨ p2) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200760473571732507217327032416 : ((p4 ∧ ((p2 → ((p1 → p2) ∧ p2)) ∧ p5)) → (((p4 → ((p5 ∧ p2) ∧ (p4 ∨ p3))) ∨ (p5 ∨ p1)) → (p2 ∨ (False ∨ (True ∨ p2))))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789885766400370404197549727289 : (((p5 ∨ (((p1 ∨ p5) ∧ p4) → ((p5 ∨ (((p4 ∧ True) ∨ (p3 ∨ p3)) → p4)) → ((True → p3) ∨ (True ∧ (p4 ∨ (True ∨ p1))))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342294073802919778371600464722 : (p2 → (((p5 ∨ p5) ∨ (((p3 ∧ p5) → p2) ∧ (p4 ∧ (p3 → (((True ∨ p3) → p2) → p5))))) ∨ (p2 → (p3 → ((p1 ∧ p4) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_533950913414295188399457181 : ((((((p5 ∨ p2) → (p3 → ((p5 → p1) → ((p2 ∧ (False ∨ (p3 → (p4 → False)))) → (p2 ∧ p5))))) ∨ False) → p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40702014633632705375849812178 : ((((((p5 ∧ p4) ∨ ((p1 → ((p1 → p3) ∨ (p3 ∨ True))) ∨ p5)) ∧ (p3 → (True ∧ (((p3 → p5) → p4) ∨ p1)))) → p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712081461076874946997486195285 : (((((p3 ∧ (True ∨ (p4 ∨ p1))) ∨ p5) ∨ (p3 → ((((p5 ∧ p4) ∧ (((p2 → ((p2 → True) ∧ p4)) ∧ p4) → p5)) ∨ True) ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228429213672736261987874614136 : ((False ∨ (p5 ∧ True)) ∨ (((True ∧ p4) → ((False ∧ p3) ∨ ((p1 ∧ (p1 ∧ p2)) ∧ ((False ∧ True) → p4)))) ∨ (((p2 ∧ False) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927604565020915103650631732863 : ((((((False → ((p1 ∨ p1) ∧ p2)) ∨ (p1 ∧ p4)) → False) ∧ ((p4 ∧ (True ∧ p2)) ∨ ((((p4 → p1) ∨ p5) ∨ p4) ∨ (False ∧ p4)))) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : ((False → ((p1 ∨ p1) ∧ p2)) ∨ (p1 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h16 : ((False → ((p1 ∨ p1) ∧ p2)) ∨ (p1 ∧ p4)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h17
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h17
            -- False on the left can always be used.
            apply False.elim h17
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h16
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : ((False → ((p1 ∨ p1) ∧ p2)) ∨ (p1 ∧ p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h22
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h21
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125039233594564077619731835542 : ((((p3 ∨ p1) → p5) ∧ ((p2 → ((((True ∨ p5) → (p1 ∧ (p5 ∧ p4))) ∨ (True ∨ ((True ∧ p1) ∧ True))) → p5)) ∧ p1)) → (p2 → p5)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173677721262322835119042111356 : ((((((False ∨ p1) ∨ p5) → (p2 ∧ (p4 → ((p5 → True) ∧ p1)))) ∨ p4) ∨ p3) → ((p3 ∧ False) ∨ ((p1 → (True ∨ False)) ∨ (False → p4)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156972870046366531653205890613 : (((((p1 → ((p2 ∧ p5) ∧ p3)) ∧ (True → (p3 ∨ p3))) → (p4 → (p2 ∨ (p5 ∨ p4)))) ∨ p2) ∨ (((p3 ∨ (p3 ∨ p1)) ∧ p1) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116657102072089546094764193220 : (((p3 → p5) ∧ ((((((p4 ∧ (p5 ∧ (p4 → p4))) ∧ (((p1 ∧ p2) ∧ False) ∧ (p3 ∧ p5))) ∧ p3) → p2) ∧ p2) → p5)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767621099616228108056897721084 : (((p5 ∧ (((True → (p3 ∨ True)) ∧ (p4 ∨ ((False ∧ p2) ∧ (((p5 → p4) ∧ ((p2 ∧ p4) ∨ (False → (p4 ∧ p4)))) ∨ False)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337542225047288063169973605463 : (p1 → (((p5 ∨ (p1 ∨ (p4 → p4))) → ((p4 ∨ (True ∨ p2)) ∧ (((p5 → p2) ∨ p1) → (p4 → p2)))) ∨ (p4 → (p1 → (p4 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142465209436096871905960770381 : ((p5 ∧ ((((((p1 → (True ∧ (False ∨ True))) → p3) ∧ p4) → (p2 ∧ p5)) ∨ True) ∨ ((p3 ∧ (True ∨ True)) → p1))) → (p3 → (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45284539277035294996184528446 : (((p2 ∧ (((p4 → (p4 → (((p2 ∧ p3) ∧ p1) ∧ p3))) ∧ p3) → ((p1 ∧ p3) ∧ ((False ∧ (p3 → p3)) → (p2 ∨ p3))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114671381859594136569682188982 : ((((False → p2) → (True ∧ ((False ∨ (((False ∨ (p4 → False)) → p4) ∧ False)) ∧ False))) ∨ (p3 ∨ (p1 ∧ ((False ∧ p2) ∨ p3)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



