variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57647551578953944022152623411 : ((((p1 ∨ True) ∨ True) → (((True ∨ (p2 ∧ (True ∨ p2))) ∧ p5) ∨ ((False ∨ ((False ∧ (p4 ∨ (False ∧ p5))) → (p3 ∧ p3))) ∨ p4))) ∨ False) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
      -- Conjunctions on the left can always be decomposed.
      let h13 := h10.left
      let h14 := h10.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46955725407760636434378934088 : (((((((p4 → (((p1 → p3) ∧ ((False ∧ p2) ∧ (p2 ∨ p4))) → (p3 ∧ True))) → (p1 → p2)) → p1) ∧ True) → p3) ∨ (p5 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678682230837549178405113360335 : (((((p1 ∨ p2) ∨ (p5 → (p2 → ((p1 ∧ (((p4 ∨ p3) ∨ p3) ∨ ((p1 ∧ p2) ∧ p5))) ∧ p1)))) ∨ (((p5 ∧ p1) → p1) ∨ False)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353191018589865708021644859761 : (p4 → (p4 ∧ ((((True ∧ ((True → False) → p3)) ∧ p3) ∨ (p5 → (p1 ∨ p3))) → ((p5 ∧ p3) ∨ (((p5 → (p2 ∨ True)) ∨ p5) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216996228318561244673516150440 : (((p5 → (p1 ∨ p2)) ∧ p4) → ((((p2 ∨ ((((p1 ∧ p5) ∧ (p2 ∨ p5)) ∧ ((p1 ∨ (False → False)) ∨ p2)) ∨ p4)) ∧ p4) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_114355684788545421768424997594 : (((p5 → (p2 ∨ (((((True → (p1 → False)) ∧ (p1 → (p2 ∨ p5))) ∧ p4) → p2) ∨ True))) ∧ (True ∨ ((True ∧ p4) ∧ p5))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_50283303635863204265398384268 : (((((p3 ∧ (((((p2 ∨ p3) ∧ p2) ∧ True) → p5) → (p4 ∧ True))) ∨ (p3 ∧ False)) → (p4 → False)) ∨ (p3 → (False ∨ (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344938434712191734041176710746 : (p3 → (((((p3 → (p4 ∧ (p2 → ((p3 → p5) ∨ True)))) → ((p3 → True) → ((p5 → p2) → (True → False)))) ∨ (p4 ∨ True)) ∨ p1) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111978948413162089583002562278 : ((((p2 ∨ (((False ∨ p3) ∧ p2) ∧ p3)) ∨ ((True ∨ ((p4 ∧ (p2 ∧ (p3 → ((False ∧ p2) ∨ p5)))) ∧ True)) ∨ p2)) ∨ p3) ∨ (p4 ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300564241583787963690336904588 : (False ∨ ((True ∧ ((True → (True ∨ ((p1 ∧ (p1 → (p1 ∨ (p2 ∧ ((True ∨ p3) ∨ p3))))) → False))) → p5)) ∨ (True ∧ ((p3 ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63938338421796420238704559582 : ((False ∨ ((((p3 → (p2 ∧ False)) → (p5 ∨ ((False ∨ (p3 ∧ p4)) ∧ (False ∧ False)))) → (p3 ∧ ((False ∧ p5) ∨ (p2 ∧ p2)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53538640538259873052211950431 : (((((p4 → ((p1 ∨ False) → (p3 ∨ p3))) ∨ p5) ∧ p1) ∧ (((p1 ∧ p3) → p4) ∨ (p4 → (p3 ∨ ((True ∧ False) ∧ (p5 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717505758153094602098274493017 : ((((p2 → ((True ∧ p3) → p5)) ∧ (p3 ∧ (((p5 → True) ∨ True) ∧ (((p2 ∧ p3) → p5) ∨ (p3 ∧ (((p1 ∧ p3) ∨ p1) ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244026596593220306788258325943 : ((True ∧ p2) ∨ ((((((((p5 ∧ (p3 → True)) → (p1 ∧ False)) → p4) ∨ True) ∧ p1) ∨ p2) → p2) → (p5 → ((p4 → False) ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123570413831735206859745447097 : ((((((p1 → p4) ∨ (((True ∧ p1) → p4) → (p2 ∨ False))) ∧ p1) ∨ (False → p5)) ∨ (p5 → ((p2 ∨ p3) → (p5 → p3)))) → (p4 → p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264138173440968998287764055376 : (True ∧ (((p4 ∨ p3) → (p2 ∨ (True ∨ (p4 → p5)))) ∧ (p5 → (((p3 ∧ p1) ∧ p5) → (((p1 ∨ (p4 ∧ (False → p3))) → p2) → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h11 : (p1 ∨ (p4 ∧ (False → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656562964539110293197798110867 : (((((p3 ∨ (p1 → (p3 → (p1 ∨ (False → p4))))) ∧ ((False ∧ (p5 ∨ (p1 ∨ p5))) ∧ ((p3 ∨ (p3 ∧ p1)) ∨ True))) ∨ (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103305877963528209277408657368 : (((p2 ∨ (((False ∧ (((True ∧ p4) ∨ p1) ∧ (True ∧ True))) ∨ p4) ∨ (p3 → (((True ∧ False) ∨ p3) ∧ (p2 → True))))) ∨ p4) ∧ (p2 → True)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340896919230970492209865465855 : (p2 → ((((p1 ∨ False) ∧ (p1 ∧ ((False → (p2 ∧ (p4 ∨ True))) ∧ p5))) ∨ ((p1 ∧ p5) ∨ (True ∨ (((p5 ∨ False) → True) → p2)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172078600342114749024800246887 : (((((False → p1) ∧ (True → p3)) ∧ ((p5 ∨ (p1 ∧ p1)) ∨ p4)) → (p2 ∧ p1)) ∨ (p2 → (p1 → (True ∨ (p3 ∧ (p4 → (p5 ∧ p5))))))) := by
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
theorem thm_5_vars_9002246800441711401798423847 : (((((((p5 ∨ (True → p2)) ∨ (p5 ∨ ((True ∧ p5) ∨ p3))) → p3) → (p2 ∨ False)) → ((((p4 → False) ∨ True) ∨ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62852276060920373260038814512 : ((p4 ∧ (((p4 ∧ (False → False)) ∧ False) ∨ (((p1 ∨ (True → p4)) ∧ p3) ∨ (((((p3 → False) ∧ (False → p2)) → p5) ∨ p1) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134950116690378399344135126608 : ((((((p1 ∧ p1) → (p2 → False)) → (p2 ∧ ((p2 → True) ∨ (p3 ∧ p5)))) ∨ (p2 ∧ (True ∨ False))) ∧ (True ∨ p5)) ∨ (True ∨ (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59336189883855336594919996639 : (((p4 ∨ p5) ∨ (((p2 ∧ p1) ∨ (p4 ∨ p1)) → (((True ∨ ((p3 → ((p1 ∨ (p3 ∨ p1)) → p1)) ∧ (True ∨ p2))) → p1) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50173574784246059423811655324 : ((((((True ∧ p1) ∧ ((((p2 ∧ ((p2 ∨ p2) ∨ p2)) → False) ∧ (p4 → p5)) ∨ p5)) ∨ True) ∧ p1) ∨ ((False ∨ (p5 ∧ p4)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138070117088462348289309397004 : ((True → (p2 → (p5 → (p3 ∨ ((((p5 ∨ (((p4 ∨ p3) ∧ (p1 → True)) ∨ (p2 ∧ p2))) → p4) ∨ p1) ∧ p3))))) ∨ ((p3 ∨ False) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213624175643125643121327930950 : ((((p3 ∧ p2) ∨ p1) ∨ p5) ∨ (p5 ∨ (p1 → (p1 → (((p5 ∧ False) ∧ (((p5 ∧ p4) → False) → (p5 → (p1 ∧ p5)))) → (True ∨ p5)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178210226270025119124762581529 : (((p3 ∨ (((p3 ∧ p2) → (True ∧ p4)) ∧ ((True → p2) ∧ True))) → p5) ∨ ((((p2 ∨ p3) → (p3 → True)) ∧ (True ∨ False)) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46107808420672910866926490302 : ((((p1 ∧ ((((False → p1) ∧ ((p1 → p4) ∧ p3)) ∨ ((False ∨ ((p2 ∨ (True ∧ False)) ∨ p3)) ∨ p5)) ∧ p1)) ∨ True) ∧ (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51754171429939823544604218314 : ((((p4 → False) ∧ (True ∧ ((False ∧ p5) → (((True → False) → p2) ∧ (p4 ∨ False))))) ∧ (((p1 → p5) ∨ p5) ∨ ((False ∨ False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40074193966447509001089216324 : ((((((((p3 → (p3 → (False → p1))) → ((p1 → (p5 ∧ False)) ∨ False)) → (p5 ∧ (p4 ∨ (p5 → p4)))) ∧ p1) → False) ∧ p2) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117748519092791617944678882866 : ((p4 ∧ (((((p5 ∧ p2) ∨ ((p4 ∨ (p3 ∨ (False ∨ (False ∨ ((p1 ∨ p4) ∧ p4))))) → p4)) ∨ p5) → (p1 ∨ p4)) ∨ p3)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110775954429000758871703514673 : (((((((p1 ∧ (p5 ∨ ((p1 → ((p3 ∨ p4) → p5)) ∨ p4))) → (p5 ∧ True)) → (p3 → (p3 ∧ p1))) ∧ p4) ∨ p3) ∧ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150721483441893911997027981275 : (((((True → p3) → ((p3 ∧ False) ∧ ((p3 → (p2 ∧ ((p1 ∨ False) ∨ p1))) ∨ (p5 ∧ p2)))) ∧ p3) ∨ False) → (((p1 ∧ p3) ∧ p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True → p3) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (True → p3) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h18
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : (True → p3) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h29 := h25 h27
    -- We need to get the left conjuct of h29 based on <expert-advice>.
    let h30 := h29.left
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- False on the left can always be used.
    apply False.elim h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205899587031263547242619996274 : ((True ∧ (p3 ∧ ((p5 ∨ True) → p4))) ∨ ((p2 ∨ (p3 → ((False ∨ ((p1 ∨ p3) ∧ (p4 → (p1 ∨ p3)))) → True))) → ((p4 ∨ p2) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117802334737283070918180257526 : ((p4 ∧ ((p1 ∧ ((p1 ∧ p2) → p2)) ∨ (p4 ∨ (p2 ∨ ((p2 → (p5 ∧ ((True → p5) ∧ p1))) → ((p4 ∧ False) ∨ p5)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_831276519733264458927983338380 : ((((p1 → (((p3 ∧ ((((p3 → p3) ∧ p5) ∧ (p5 → p1)) ∧ ((p5 ∧ p2) ∧ (True ∧ False)))) ∧ ((p5 → p1) → p5)) ∧ True)) ∧ p1) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719000849518979573736381264703 : (((((False → p4) → (p4 ∧ p2)) ∨ ((((p4 → ((True → p3) ∧ p5)) → p5) → p1) ∨ ((((p1 → (p2 → True)) ∨ p4) → False) → p2))) ∨ p3) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (p2 → True)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718432970157944559918497700946 : (((((True ∧ (p4 ∨ p5)) → False) ∨ (p1 ∨ ((((p2 ∧ ((p4 ∨ p4) ∨ p4)) ∧ False) ∨ (((True → False) ∧ (p5 → p5)) → p1)) ∨ p1))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166108744952223056620677217527 : (((p4 → p2) → ((p2 → (((((False ∨ (p2 ∨ True)) ∧ p4) → p5) ∨ False) ∨ True)) ∨ p5)) ∨ (((p5 → (p5 ∨ p4)) → (p5 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208116731157184058059977274430 : ((((p2 ∧ p1) ∨ True) → (False ∧ p4)) → (((False → ((False ∨ False) → p2)) → p5) → (p3 ∨ (((True → ((p4 → False) → p4)) → False) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715141196659546298260315159953 : ((((p5 ∨ ((p3 → p2) ∧ (True → p5))) → ((False ∧ p3) ∨ ((p5 → False) ∨ (p3 ∨ (((p4 → p2) ∧ (p4 ∨ p3)) ∨ (p4 → p4)))))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51190069787145158807940218169 : ((((False ∧ ((p3 → ((True ∧ (p4 ∨ p5)) ∨ (p2 ∨ p3))) ∨ p5)) ∨ (p4 ∧ (p5 ∨ p5))) ∨ (False ∨ ((p3 → p4) → (False → True)))) ∨ p1) := by
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
theorem thm_5_vars_629538562490150308341973415075 : ((((((((((True ∧ ((False ∨ p3) ∨ p1)) ∨ False) ∨ (p4 → p4)) ∨ p5) → (p1 ∧ ((p4 → True) ∨ True))) → (p1 ∨ True)) ∨ p1) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47385491722217070321144451894 : ((((p3 ∨ p5) → ((False ∧ ((True → (p2 ∨ (p4 → (((p2 ∨ (p4 → p1)) ∨ p4) → p4)))) → p4)) ∨ (False → p3))) ∨ (p4 ∨ False)) ∨ p1) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655396882094701895406430090065 : ((((((((((p2 ∨ p2) → p5) ∨ (p3 ∧ p2)) ∨ p1) ∧ (p4 → (p3 ∧ p1))) → (p2 ∧ (p4 ∧ False))) ∨ (p5 → True)) ∨ (p2 ∧ True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198644192861338609585291670628 : ((p3 ∨ ((p4 ∨ (True ∧ p5)) → (p4 ∧ False))) ∨ (p3 → ((p5 ∨ ((((False ∧ ((p4 ∨ True) ∧ False)) ∧ p5) ∨ p3) ∨ False)) ∧ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354043593442147715459330554843 : (p4 → (p4 → ((p1 ∨ (p3 ∨ ((True ∨ (p1 ∨ p3)) ∧ p1))) ∨ ((True → (((p3 ∨ (p3 ∧ (p5 ∨ p1))) ∨ p4) ∨ (p1 → p4))) ∧ True)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208407043755855060958258992045 : (((False ∨ p3) ∨ (p1 ∧ (p1 ∨ p4))) → (((p3 → p5) → p2) ∨ ((True → p5) ∨ ((p3 ∧ (((p2 ∧ (p5 → p1)) ∧ p1) ∧ True)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h28
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- One of the premise coincides with the conclusion.
      exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246168346843171118067538574333 : ((p4 ∧ p2) ∨ ((p1 → p1) → (p4 → ((p5 ∨ ((p5 ∨ p2) ∧ (p5 → True))) ∨ (((False ∧ ((p3 ∧ (p5 ∨ False)) ∨ p1)) ∧ p1) → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217692017295560735050222683822 : ((((p4 → p4) → p1) → True) → ((((p4 ∨ (True ∧ (p5 ∨ (((p5 ∧ (False → True)) ∨ p1) ∨ p2)))) → True) → ((p2 ∧ p5) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597854813189980950193172282 : (((True ∨ (p4 ∨ (((True ∧ (p3 ∨ p1)) ∨ p4) ∨ (((p5 ∧ (True ∨ ((p2 → True) ∧ p3))) → p5) ∨ (p2 ∨ p2))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681644922801874600635295825106 : ((((p3 → (((((p2 → (p2 ∧ p1)) → p1) → p5) ∨ p3) → ((p5 → (False ∨ (p1 ∧ False))) ∧ p4))) → (p5 ∨ (p1 → (p2 ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605379432824285005339982703188 : ((((p3 → ((p4 ∨ ((((p1 ∨ (((p1 ∨ False) → p3) ∧ (p2 ∧ p4))) → (p5 ∨ (True ∨ p5))) ∧ True) → p4)) ∨ (p2 ∧ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113518648919691859590146673969 : ((((p4 → ((p1 → ((True ∧ (p3 ∧ p4)) → p2)) → p2)) ∧ ((False ∨ ((p3 ∨ (True ∧ p1)) ∧ False)) ∨ False)) ∨ (p1 → True)) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63354295041212671460731495995 : ((p5 ∧ (p1 ∧ (p2 → (p5 ∨ (p1 ∨ ((p1 ∨ p4) → (p3 ∧ (True ∧ (p5 → ((True ∨ p1) ∧ (True → ((p2 → p1) → p3)))))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55513869888843595473009982230 : ((((p2 ∧ True) ∨ (p2 → (p5 ∨ False))) → (False ∨ ((p1 ∧ (p1 → p3)) → (p2 ∧ ((p1 ∧ (p1 ∧ False)) ∧ (p3 → (p5 ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81086856241627481583752013592 : ((((False → (p1 → (p4 ∧ p4))) → (((p4 → (((p2 → p2) ∨ p2) → True)) ∨ (False ∧ (p2 → False))) ∧ False)) ∧ ((p5 → False) → True)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → (p1 → (p4 ∧ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327191232086007511769067635072 : (True → ((p3 ∨ ((p5 ∧ (((p2 ∨ False) ∨ (p3 → p1)) ∧ p3)) ∨ ((((p1 ∨ p5) ∧ p1) ∨ p4) → ((False ∨ (p1 ∧ p2)) ∧ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147163388205067285005747460067 : (((p5 ∧ ((((p1 → (p3 → p1)) ∨ p1) ∧ False) ∧ ((p5 → (((p1 ∧ False) → True) → p2)) → False))) ∧ True) ∨ ((True ∧ False) → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199468359137265748097964725380 : (((False ∨ (True ∨ ((p4 ∧ p1) ∨ True))) ∨ p2) → ((p4 ∧ (((p2 ∨ p4) ∨ True) ∧ (p4 → ((False ∧ (p5 ∨ False)) ∧ p1)))) → (p4 → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h14 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h4
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h15 := h7 h14
            -- We need to get the left conjuct of h15 based on <expert-advice>.
            let h16 := h15.left
            -- We need to get the left conjuct of h16 based on <expert-advice>.
            let h17 := h16.left
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Conjunctions on the left can always be decomposed.
              let h20 := h19.left
              let h21 := h19.right
              -- One of the premise coincides with the conclusion.
              exact h21
            case inr h22 =>
              -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
              have h23 : p4 := by
                -- One of the premise coincides with the conclusion.
                exact h4
              -- We have shown the premise of h7, we can now drive its conclusion.
              let h24 := h7 h23
              -- We need to get the left conjuct of h24 based on <expert-advice>.
              let h25 := h24.left
              -- We need to get the left conjuct of h25 based on <expert-advice>.
              let h26 := h25.left
              -- False on the left can always be used.
              apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h28 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h29 := h7 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- We need to get the left conjuct of h30 based on <expert-advice>.
        let h31 := h30.left
        -- False on the left can always be used.
        apply False.elim h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h37 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h32
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h38 := h7 h37
            -- We need to get the left conjuct of h38 based on <expert-advice>.
            let h39 := h38.left
            -- We need to get the left conjuct of h39 based on <expert-advice>.
            let h40 := h39.left
            -- False on the left can always be used.
            apply False.elim h40
          case inr h41 =>
            -- Disjunctions on the left can always be decomposed.
            cases h41
            case inl h42 =>
              -- Conjunctions on the left can always be decomposed.
              let h43 := h42.left
              let h44 := h42.right
              -- One of the premise coincides with the conclusion.
              exact h44
            case inr h45 =>
              -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
              have h46 : p4 := by
                -- One of the premise coincides with the conclusion.
                exact h32
              -- We have shown the premise of h7, we can now drive its conclusion.
              let h47 := h7 h46
              -- We need to get the left conjuct of h47 based on <expert-advice>.
              let h48 := h47.left
              -- We need to get the left conjuct of h48 based on <expert-advice>.
              let h49 := h48.left
              -- False on the left can always be used.
              apply False.elim h49
      case inr h50 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h51 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h52 := h7 h51
        -- We need to get the left conjuct of h52 based on <expert-advice>.
        let h53 := h52.left
        -- We need to get the left conjuct of h53 based on <expert-advice>.
        let h54 := h53.left
        -- False on the left can always be used.
        apply False.elim h54
  case inr h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- False on the left can always be used.
        apply False.elim h57
      case inr h58 =>
        -- Disjunctions on the left can always be decomposed.
        cases h58
        case inl h59 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h60 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h61 := h7 h60
          -- We need to get the left conjuct of h61 based on <expert-advice>.
          let h62 := h61.left
          -- We need to get the left conjuct of h62 based on <expert-advice>.
          let h63 := h62.left
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- Disjunctions on the left can always be decomposed.
          cases h64
          case inl h65 =>
            -- Conjunctions on the left can always be decomposed.
            let h66 := h65.left
            let h67 := h65.right
            -- One of the premise coincides with the conclusion.
            exact h67
          case inr h68 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h69 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h4
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h70 := h7 h69
            -- We need to get the left conjuct of h70 based on <expert-advice>.
            let h71 := h70.left
            -- We need to get the left conjuct of h71 based on <expert-advice>.
            let h72 := h71.left
            -- False on the left can always be used.
            apply False.elim h72
    case inr h73 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h74 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h75 := h7 h74
      -- We need to get the left conjuct of h75 based on <expert-advice>.
      let h76 := h75.left
      -- We need to get the left conjuct of h76 based on <expert-advice>.
      let h77 := h76.left
      -- False on the left can always be used.
      apply False.elim h77



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43167073818812456599824333120 : ((((((p5 → p2) ∨ p3) ∨ ((p3 ∨ ((p3 → (True → ((False ∨ (True ∧ (p2 ∧ (p4 ∧ p5)))) ∨ p1))) → p4)) ∨ p3)) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227556677172357934268132847336 : ((True ∧ (p3 → p5)) ∨ ((((False ∨ (False ∧ p3)) ∨ (p2 ∧ p5)) ∧ (((((True ∧ p1) → p4) ∨ p5) → p4) ∧ ((p4 ∧ True) ∨ True))) → p5)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336200163116310823573201692348 : (p1 → (((((p2 → (p1 ∧ True)) → ((p2 ∨ p1) → p3)) ∧ (((((p4 ∧ p4) ∨ (p3 → p4)) → p3) → p2) ∧ p4)) ∨ (p3 → p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42235690692972245381018474924 : (((False ∧ ((p4 ∧ p2) ∧ (((((False ∨ p4) → True) → p4) → ((((True → p4) ∨ p1) → (p2 ∨ True)) ∨ p5)) ∨ (True ∨ p5)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165856391829985655679077690374 : (((p2 ∧ (p2 ∨ p5)) ∨ ((((p1 ∧ ((p1 ∨ p1) → p1)) ∧ p4) ∧ (p4 → False)) ∨ p3)) ∨ ((((p3 ∨ p4) ∨ p3) ∨ (p3 → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729157354652154844630519420563 : (((((p1 → p4) ∧ p4) → (((p3 ∧ True) → p4) → ((((p3 ∧ (False ∧ (True → ((False ∧ False) ∨ False)))) ∨ p4) ∨ (False ∧ p1)) ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38672682749891790176887823345 : ((((((p2 ∧ p2) ∧ True) ∧ (p5 ∨ p4)) ∧ (((((((p5 → (p1 ∧ True)) ∧ p1) ∨ p3) ∨ p3) ∨ p4) ∨ (p5 ∨ p3)) ∧ False)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47594486391088350440881475762 : (((p3 → ((((p5 ∧ (p3 ∨ (p2 ∨ ((p4 ∨ True) ∧ ((p3 → False) ∧ (False ∨ p3)))))) ∧ (True → p1)) ∨ p4) ∨ p4)) ∨ (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348502840597688203033101261942 : (p3 → (p3 ∧ (((((p2 ∧ False) ∨ ((True ∨ p5) ∨ (p4 ∨ (True ∧ (p3 ∧ p2))))) ∧ p2) ∧ (p3 ∨ p4)) → (p1 ∨ (p1 → (p2 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- Implications on the right can always be decomposed.
          intro h25
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Implications on the right can always be decomposed.
          intro h30
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- Implications on the right can always be decomposed.
          intro h41
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h43
          -- Implications on the right can always be decomposed.
          intro h44
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49725661915009348632991391989 : (((p1 ∧ ((((p1 ∨ p2) ∨ p3) → (((False ∧ ((False ∧ True) ∧ p4)) ∧ p4) ∨ p3)) ∧ (True ∨ (p5 ∨ p3)))) → (p2 ∨ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749694101271334899047138839712 : (((True ∧ ((((((False ∧ (False ∨ p3)) ∧ (True → p3)) → (p4 ∨ p3)) → ((p4 ∧ p4) ∧ ((p1 ∧ p2) ∧ p1))) → (p5 ∧ p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323639048005364341210469344143 : (p5 ∨ ((p2 ∨ ((p1 ∨ (p5 ∨ ((p3 ∨ (p5 ∧ True)) ∨ (p2 ∧ ((False ∧ p2) ∨ (True → p3)))))) ∨ True)) ∧ (((p4 → True) → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196127490202392921343478487243 : ((True ∨ ((((False ∧ p1) → False) → True) ∨ p5)) ∧ (((p1 ∧ ((False → True) → (((p1 ∧ p5) ∨ p3) ∨ p4))) ∨ (True ∨ (p4 ∧ p2))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_149130264472683154345774409227 : (((p3 ∧ p1) ∧ (((((p2 → (p3 ∧ p5)) ∨ (p5 ∨ p5)) ∨ ((p2 ∧ p3) ∨ True)) ∨ (p3 ∨ p3)) ∨ p2)) ∨ (((p3 ∧ p1) ∧ False) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149958747346590544339511506294 : ((p4 ∨ (((p3 ∧ (((True ∧ p5) → (p4 ∨ p1)) ∧ p2)) → (False ∨ (((p3 → p3) ∨ p3) → p5))) ∨ p5)) ∨ (p1 ∨ ((p4 → p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327109712368609070965987259762 : (True → (((p2 ∨ False) ∨ (((p4 ∨ p2) ∧ ((p1 ∨ (False → ((((True → p1) ∧ p1) → p2) → p2))) → ((p3 → p2) ∧ p4))) ∨ True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114364602303139289405602250911 : ((((p3 → ((p2 → False) ∨ ((((p1 ∨ (p3 ∧ p2)) ∧ p3) ∨ p2) ∧ (True ∨ p2)))) ∧ p1) ∨ (False ∨ (p5 ∧ (p5 ∧ True)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135819756789669018663193637670 : ((((((False ∨ (p2 ∧ p4)) ∨ ((p3 ∨ False) ∧ True)) ∧ p4) → p1) ∧ ((((p3 → True) ∨ p2) → (p4 ∨ p4)) ∨ p4)) ∨ (p2 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110981299283518699543206466278 : (((((((p1 ∧ (p1 ∧ ((True ∨ p3) → False))) ∨ p2) → p5) → (True → (p5 ∨ (p3 ∨ (p5 ∧ p5))))) → (p3 ∨ False)) ∧ p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166154624692040832690455585287 : ((False ∧ (((p2 ∧ False) → ((p2 ∨ (p2 → (p2 → (False ∨ (False → False))))) ∧ True)) → p2)) ∨ ((p2 → (False ∧ p1)) → ((False → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164113895547011937714744626098 : ((p2 ∨ (p1 → ((p2 ∧ ((p4 → (p2 ∧ p1)) → (p4 ∧ p3))) ∨ ((p5 → True) ∨ p2)))) ∧ ((True ∨ p1) ∨ (p1 ∨ ((False ∨ p5) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4649408135129029916442755382 : (p5 → (((((((((False → p2) ∨ p1) ∧ p4) → p1) ∨ ((p2 ∧ False) → False)) ∨ p2) → p4) ∧ True) → ((p1 ∨ (p2 ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703503675811340555038219986213 : ((((True → (p5 ∨ (((p2 ∨ (p4 ∨ p2)) ∧ p2) ∨ True))) ∨ ((True → (False ∧ False)) → (p2 ∧ (True → ((p4 → p3) ∨ (True ∧ True)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55137340795376066599228204153 : ((((p4 → ((p2 → p4) → p2)) ∧ p4) ∨ ((p4 ∨ (p2 ∨ (True → True))) ∨ (True → ((((False ∧ p2) ∨ (True ∨ p1)) → True) ∧ p4)))) ∨ False) := by
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
theorem thm_5_vars_340965479207041760530877575041 : (p2 → (((p4 ∧ p3) ∧ (p2 ∧ (((p2 → (p4 ∨ ((False → True) ∨ p5))) ∧ (p3 ∧ p1)) ∧ (p5 ∨ ((True ∧ False) ∧ (True ∨ p3)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180973338701480828271298223135 : (((p3 → p5) ∧ (((((p1 → (False ∨ p4)) ∨ False) ∨ False) ∨ p1) ∧ p2)) → (((True ∧ ((False ∧ p4) ∨ (False ∨ True))) → p4) → (p4 ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (True ∧ ((False ∧ p4) ∨ (False ∨ True))) := by
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
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (True ∧ ((False ∧ p4) ∨ (False ∨ True))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216058254705984274305799265412 : ((p5 ∨ (p1 ∨ (p1 ∨ False))) ∨ ((p2 ∧ (p3 ∨ p1)) ∨ ((p3 ∧ (p4 ∨ (False ∨ (p5 ∧ (p1 ∧ ((False ∨ p1) ∨ p4)))))) → (p3 ∨ True)))) := by
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
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46620676118751926824740418472 : (((p3 ∧ (p1 ∧ (((p3 → (p3 ∧ (((p3 ∧ (p2 ∨ (p1 ∨ True))) ∨ p5) ∧ (p4 ∨ p5)))) ∨ p4) → (p5 ∧ p4)))) ∧ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618609273744333624581690911840 : (((((p2 → (p2 ∧ (p5 ∨ p2))) → ((((p3 ∧ ((False → False) ∨ True)) ∧ (p2 ∧ (p1 → p5))) ∨ ((p2 → True) ∨ p2)) ∧ True)) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347923895965670076726253977348 : (p3 → ((True ∨ p4) ∧ ((p5 ∨ p5) → ((p3 ∧ (p5 ∨ (p3 ∧ (p5 ∧ p2)))) → ((p2 → (((True → False) ∨ (p1 ∨ False)) ∧ p3)) ∨ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
theorem thm_5_vars_40196037365280747239720363282 : ((((((p1 → p3) → p3) → ((((p1 → p3) → p2) ∧ (p4 ∧ ((p1 ∧ (p3 ∧ True)) → (p4 → p4)))) ∨ (True ∧ p4))) ∧ True) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41596678914065791089604000261 : (((((p4 ∧ (p3 → (p1 ∨ (p3 ∧ p5)))) ∧ True) ∨ ((p5 ∧ (p4 → p3)) ∧ ((((p2 ∧ (p2 ∨ p5)) ∧ p2) → p5) ∧ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185667922091441047784639952534 : ((p1 → ((p2 ∧ (p5 ∨ (p5 ∧ (p1 → (p2 → p5))))) ∧ False)) ∨ (False → ((True → p4) ∨ ((p4 ∨ (p3 → True)) ∧ (p4 ∧ (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119113133833779501383261789054 : ((p1 → ((p3 ∨ False) ∨ (((False ∧ (((True ∧ (p3 ∨ (p5 → (p1 ∧ p2)))) ∨ (p1 → True)) ∨ True)) ∨ True) ∧ (p5 ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798249197015952434614316900641 : (((p1 → (((((False ∨ p4) ∧ (True ∨ (p3 ∧ True))) → (p2 ∨ ((False ∨ p3) ∧ p3))) → p3) ∨ (False ∧ (p5 ∧ (p3 ∧ (p1 ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40299516742226233222788505660 : ((((((p2 → (((p5 ∨ ((False ∨ p1) ∧ True)) ∧ p4) ∨ (p1 ∨ (p3 → ((p1 → False) → (p5 ∨ p5)))))) ∧ False) ∧ p3) ∨ p3) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38740213672117279098464238180 : ((((((p3 ∧ p3) ∨ True) ∧ p2) ∧ (p1 ∨ (p5 ∧ (False ∨ ((((True ∧ False) → p3) → (True ∨ p4)) → ((True ∧ p5) ∧ p2)))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54581145268887373373841046641 : (((p2 ∨ (p3 ∧ (((False ∧ False) ∨ p3) ∧ True))) ∨ ((p1 ∨ (True ∧ (p1 ∨ ((False ∧ p2) → ((p1 ∨ False) → (p3 ∨ True)))))) ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116406752844058863545897971517 : (((True ∨ (p1 ∨ p1)) → ((((p1 → p5) ∨ True) ∧ ((p3 ∨ (p5 ∨ p2)) ∧ (True ∧ p4))) → ((False ∧ p5) ∨ (False → p1)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



