variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753737072521019203843557230564 : (((False ∧ (((p2 → False) ∧ ((True → (((p3 → p5) ∨ p4) ∧ True)) ∧ False)) ∧ ((((((p2 ∧ False) ∨ False) ∧ p2) ∨ p3) ∧ False) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68916861563861391860808354600 : ((p4 → (p1 ∨ ((((p3 ∨ p5) ∨ (True ∧ (p4 ∨ (((p4 → False) ∨ False) → ((True ∧ p1) ∨ False))))) ∧ p3) → (p4 → (p2 ∨ True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142201228540254701868517017719 : ((p1 ∧ ((p1 ∨ ((p1 ∨ p5) ∨ (p2 ∨ ((p3 ∧ (True → (p4 ∧ False))) ∧ True)))) ∨ (p1 → (p4 ∧ (p5 → False))))) → ((False ∧ p2) ∨ True)) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Conjunctions on the left can always be decomposed.
          let h15 := h13.left
          let h16 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111512333090284198534090578841 : (((p5 → ((p3 ∨ (p3 ∨ (((((p5 ∨ True) ∧ p2) ∨ False) ∧ (p5 → (p4 → (p1 ∨ (p2 ∧ p2))))) → p4))) ∧ p2)) ∧ True) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354599220156750899780482877138 : (p5 → ((((((True ∧ p4) ∨ p2) ∧ (p1 → ((p1 ∨ (p1 ∨ p4)) ∧ (p3 ∨ ((p1 ∨ ((p4 ∨ True) ∧ True)) ∨ p4))))) ∧ p3) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113216245386354758925724962788 : ((((p2 ∨ (p4 ∨ ((p5 ∨ (((p4 ∨ p1) → p4) ∧ (((p1 ∨ False) → p3) ∧ (p4 → p3)))) ∧ p2))) ∨ True) ∧ (p4 → p2)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782039229197572395029229015438 : (((p2 ∨ (p5 → (((p3 → ((False ∨ True) → p2)) ∨ p1) → ((((((p3 ∨ p3) → (False ∧ (p4 ∧ p3))) → p5) ∧ p2) ∨ p3) ∨ True)))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50674769294693938646642136460 : (((((p1 ∧ (p3 → False)) ∧ p4) ∧ (((p3 → True) → p1) → ((((True → p4) ∨ False) ∧ p3) ∨ p4))) → (True ∧ (p5 ∧ (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710890806998701115235999012113 : (((((False ∧ p2) ∨ ((p2 ∧ p4) → p5)) ∧ ((False ∧ (((True → ((p4 ∧ True) → p3)) ∧ p4) ∨ p4)) ∨ (((False → p5) → False) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61244177201741895183011060760 : ((False ∧ (p4 ∧ ((p5 ∧ True) → ((((False ∨ p4) ∧ (False ∧ ((p5 → p4) ∧ ((True ∧ False) ∧ p2)))) ∧ (p4 ∧ (False → p1))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66359109470323853935432881098 : ((p5 ∨ (False ∨ (((p2 ∧ ((p3 → p2) ∨ (((((p4 → (p1 ∧ p3)) → p4) ∧ (p3 ∨ p3)) → p5) ∨ p5))) → (p1 → p1)) ∨ False))) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668917572435613195122848130620 : (((((p3 ∧ (p1 ∧ ((((((False → p2) → p5) ∨ (False ∨ (p2 ∨ p3))) → p1) ∨ (p3 ∨ p2)) ∨ False))) ∨ p1) ∨ ((p1 → True) ∨ p5)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115167491247028860618009742557 : (((((False ∨ (p5 ∧ (True ∨ (p4 ∨ p3)))) ∨ p2) ∨ False) ∧ ((True ∧ ((p3 ∧ p4) ∨ p3)) ∨ ((p2 → p2) → (False ∧ p3)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40041457473821174933282779254 : (((((p2 ∧ (p1 ∨ (p5 → (((p2 → ((True ∨ (False → ((p3 ∨ p5) → p4))) ∨ p2)) ∨ (p5 → True)) ∧ p1)))) ∧ p5) ∧ True) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677714620211699440413876382627 : (((((((True ∨ p1) → False) → (p3 ∧ (p3 → (p4 ∧ (((p5 ∨ p3) → False) ∧ (p3 ∨ True)))))) → p2) ∨ ((p3 ∨ True) → (False ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56078656653034621746224638029 : ((((p3 ∨ (p1 → False)) → p4) ∨ (p5 ∧ ((p3 → (((p1 ∨ p2) ∧ (((p2 ∧ p2) ∨ p4) → p5)) ∧ (False → p3))) ∨ (True → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137110299805898935920031086918 : ((True ∧ ((((True → (p1 ∨ p2)) → (p1 ∧ (p5 ∧ (p1 ∧ p4)))) ∧ p4) ∧ ((p4 → True) ∧ ((p5 → p4) → p3)))) ∨ (p4 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322457734436153548899918825889 : (p5 ∨ (((p5 → (p3 ∧ p3)) ∧ ((p2 ∨ ((p1 → ((p1 ∧ p3) ∧ ((False ∧ (p5 ∧ p1)) ∨ p2))) → True)) ∧ ((p1 → p5) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179707514523087313574970917025 : (((((p1 → p3) → (((p1 ∨ p3) ∨ (True → True)) → p4)) ∨ p4) ∧ p3) → (((p4 → p5) ∨ p4) ∨ (((True ∧ (True → True)) ∧ p1) ∧ False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∨ p3) ∨ (True → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160558632193950919105679633691 : ((((((p1 → (p3 → (True ∨ p1))) → (False ∨ p1)) ∨ p4) → p5) → (((True ∨ p2) → False) ∨ p4)) → ((p2 ∨ (p4 ∧ (p4 → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21524751669246083943584741450 : ((((p3 → p2) → (((p4 ∧ (p1 ∨ p5)) → p5) → p1)) ∨ (True ∨ (True ∨ (p4 → ((p4 → ((p3 → (False → p1)) ∨ p2)) ∨ p1))))) ∧ True) := by
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
theorem thm_5_vars_246520706853826781892697743926 : ((p5 ∧ p1) ∨ (((True ∧ True) → (True → (p1 → ((p3 ∨ False) → p4)))) → ((((p3 ∧ True) → ((False ∨ p2) ∧ (p3 → False))) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153042458013773427086637697910 : ((p2 ∧ (p1 ∨ ((p1 ∨ ((p4 → False) → (((p1 ∧ (p1 ∨ False)) ∧ (p4 ∨ (True ∨ False))) ∨ True))) ∧ p1))) → ((p3 → p4) ∨ (p2 → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
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
      exact h8
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305033913872497855868765042135 : (p1 ∨ ((p5 ∨ (((p2 ∨ False) → (p1 ∧ ((False ∨ ((True → p5) ∧ (p4 ∨ p2))) ∧ ((True ∧ False) ∨ False)))) ∨ False)) ∨ ((True ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147491931418467053465723132229 : (((p5 ∧ (p1 ∨ ((p2 ∧ (((p5 ∨ p5) ∨ ((p1 ∨ False) ∧ True)) ∨ (True ∧ (p3 → p2)))) ∨ p2))) ∨ p4) ∨ (((p2 ∧ p1) → p2) ∨ p2)) := by
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
theorem thm_5_vars_134126401330726826066220974586 : ((((False ∨ ((((False ∨ (False ∨ p3)) ∧ (p5 ∨ ((False → p3) → (p4 ∧ True)))) → p4) → p4)) ∨ (False ∧ False)) ∨ True) ∨ (p1 → (False ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116522455700052106078534346212 : (((p5 ∧ p3) ∧ ((p5 ∧ p2) ∨ (((((((p1 ∧ True) ∨ p1) → p2) → p5) ∨ (p5 → (p1 → (True → p5)))) → False) ∨ p1))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54566439507506137252399164387 : (((p5 ∧ ((p1 → p5) → (p5 ∨ (p2 → p5)))) ∨ ((p2 ∨ (False ∨ ((True → (p1 ∧ ((p5 ∧ p2) ∨ False))) ∧ p1))) ∧ (p2 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354763824484849406354312954978 : (p5 → (((p3 ∨ ((p2 → False) → ((p2 ∧ False) ∨ (p4 → (True → p5))))) ∧ (((True ∧ p1) → ((p1 ∧ (True ∨ p2)) ∨ p1)) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119265059046527636002053857053 : ((p2 → (p3 → ((p5 → (False ∧ (p3 ∧ p2))) → (((True → False) ∨ True) ∧ ((False ∧ (False ∨ (True ∧ (True ∧ False)))) ∧ False))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56681791230638995945343546034 : ((((p4 → True) ∧ p5) ∧ (((False → (p2 ∧ (False ∨ (p5 ∨ ((p2 ∧ p1) → (p1 → True)))))) → False) ∨ ((p5 ∨ (p1 ∨ p4)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114166121091841611825952493573 : ((((p3 ∧ ((((p5 ∨ (p1 ∨ p4)) → p1) → ((p5 → False) ∧ ((p1 ∧ False) ∧ True))) → p4)) → True) → (True → (p5 ∨ p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1798646419351730256720962179 : ((((p3 → p4) ∨ p1) → (((p1 ∧ True) ∨ p4) ∧ (((p2 → (p5 ∨ p5)) ∨ p4) → (p4 ∨ (p1 → p3))))) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114072294174089207866371306752 : ((((((p3 ∧ True) ∧ p2) ∧ False) ∧ (((((p3 ∨ (p1 → p5)) ∨ True) ∧ False) ∧ (p3 ∧ p4)) ∧ p4)) ∨ (False ∨ (True ∨ p1))) ∨ (p4 ∧ p4)) := by
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
theorem thm_5_vars_177863788141657264322422424255 : (((((p1 → p3) ∨ ((((p3 ∧ p5) ∧ p5) ∨ p1) ∨ p4)) ∨ p2) ∨ True) ∨ (p5 ∨ ((False ∨ (p4 ∧ p1)) → ((p3 ∧ p5) ∧ (p4 ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249963564282505677391215359741 : ((True → p2) ∨ (((p5 ∨ (((p5 → True) → ((p3 → (((True ∨ p1) ∧ False) ∧ p1)) ∨ (((p3 ∨ p5) ∧ p3) ∨ True))) ∧ True)) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((p5 → True) → ((p3 → (((True ∨ p1) ∧ False) ∧ p1)) ∨ (((p3 ∨ p5) ∧ p3) ∨ True))) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234618269105633727131188534321 : ((p3 → (True → p3)) → (p1 → (((((((p1 → p2) → False) ∨ p1) ∧ (p3 ∨ p2)) ∧ ((True ∧ ((False ∨ p2) → p3)) → p4)) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_214506988697696073468723226222 : (((p3 ∧ p3) ∧ (p2 ∧ p4)) ∨ (((p2 ∧ p3) ∧ ((((p5 ∨ (p5 → (((p3 ∧ p5) ∨ p2) → p1))) ∧ p1) ∧ p1) ∨ True)) → (p4 ∨ True))) := by
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
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
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765178543153897779551799327474 : (((p4 ∧ ((p1 → ((p2 ∧ False) ∧ (False ∧ ((False ∧ p2) ∧ (((p5 ∨ p3) ∧ p2) ∨ ((p5 ∨ p4) → (p2 → False))))))) ∨ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60599289856996141498610359794 : ((True ∧ ((((p5 ∧ (((p4 ∧ (p2 ∧ (p2 ∨ (p4 → (False ∧ (True ∨ (p3 ∨ False))))))) ∨ p1) ∧ True)) ∨ p4) ∨ p5) ∧ (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728036050661100663041765941435 : ((((p4 ∨ (False ∧ p3)) ∨ ((((((True → (p4 ∧ ((p3 ∧ (False ∨ False)) ∧ ((p1 ∧ p5) ∧ True)))) ∧ p2) ∨ True) ∨ p4) ∧ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193446997219100793549529660351 : (((p3 → False) ∧ (((False → False) ∧ p3) ∨ (p3 ∧ p4))) → ((((p5 ∨ p4) → (True ∧ p4)) ∨ (p5 ∨ p3)) ∧ ((True ∧ (p5 ∧ p5)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
    exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h16 := h10 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h20 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h21 := h10 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h27 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h28 := h22 h27
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h32 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h33 := h22 h32
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336226713756287457299722982274 : (p1 → (((((p3 ∨ p2) ∧ p1) → ((((p1 ∧ p3) → p3) ∨ p4) → (p5 ∧ (False ∧ (p1 → (p3 ∧ False)))))) ∨ ((False ∨ p3) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622058982527969224351724439927 : ((((p2 ∧ ((p1 ∨ (((p1 → (False → ((p2 ∧ p2) ∧ (p3 ∨ ((p1 ∧ (p5 ∧ p1)) → False))))) → (p3 → p1)) → True)) → p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_662547105113970634603756887519 : (((((p5 ∨ (True → (p3 ∨ (p1 → p5)))) ∨ ((False ∨ (p5 ∨ ((p5 ∨ ((False ∧ p2) ∧ p2)) ∨ p4))) → (p2 ∨ p2))) → (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608945197708268018047500503320 : (((((((False → (p3 ∨ (p3 ∧ ((False ∨ False) ∧ p2)))) → (p3 ∧ True)) ∧ (p1 → ((p3 ∨ p1) ∧ (p1 ∧ (p2 ∨ p3))))) ∨ True) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52419249765480075372452451572 : ((((True ∨ p1) ∧ (p2 ∧ (p5 → (p1 ∧ (p2 ∧ ((p2 ∨ p5) → p3)))))) ∧ (p2 ∨ ((p2 ∨ p2) ∨ ((p1 ∧ (p4 ∧ p5)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118836386005403751057376237479 : ((True → (((p2 → (p1 → (p4 ∧ (((((p2 ∧ (True → (p2 ∧ True))) ∨ False) ∧ p4) ∨ p1) ∨ p3)))) ∨ False) → (p4 ∧ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68088790213483707268401251050 : ((p2 → (p5 ∨ ((False ∨ ((p3 ∧ (True ∨ p4)) → ((p3 → (p1 ∨ p2)) ∧ (p2 → ((p5 ∨ True) → (p4 ∨ p3)))))) ∨ (True ∨ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_52907093146770029902447562276 : (((p1 → (p5 ∨ (((p2 ∧ True) ∧ p2) ∨ (p4 → ((p2 ∨ p5) ∧ p2))))) → ((((True ∨ p5) ∧ True) ∧ (p5 → (False ∨ p5))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919905547803205356498772708741 : ((((p2 → (((False ∨ (p4 ∨ False)) ∨ (((p5 ∨ p4) ∨ p5) ∧ p4)) ∧ p3)) ∧ ((p4 ∨ (p3 ∨ (p4 ∨ p2))) ∧ ((p3 ∨ p4) → False))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p3 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : (p3 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : (p3 ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : (p3 ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h19 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h20 := h2 h19
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h22 := h5 h18
        -- False on the left can always be used.
        apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58857268662901163984503298241 : (((True ∧ p4) ∨ ((((p1 → (False ∨ (True → p3))) → ((p1 ∧ False) ∧ p5)) → (p4 → (p1 ∨ p3))) ∨ (True ∨ ((p2 ∧ p4) ∧ p1)))) ∨ False) := by
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
theorem thm_5_vars_246784510788844966031299161401 : ((p5 ∧ p5) ∨ (p2 ∨ (((p4 ∧ p2) ∧ True) ∨ ((p1 → (False ∨ ((p5 ∨ (p4 → (p5 ∧ True))) ∨ (p2 → True)))) ∨ (p1 → (True ∧ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710643921619553736161583142270 : ((((((p1 ∨ False) ∨ p1) ∨ (p3 ∨ p2)) ∧ ((p5 → p2) ∨ ((((p2 ∧ p5) ∨ (p4 ∧ (p2 ∨ False))) → (False ∧ True)) ∧ (p1 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350255068288343491652560942768 : (p4 → ((p1 ∧ ((False ∧ (((p5 → (p2 ∨ ((True → p4) ∧ ((p4 → p3) ∧ (p3 ∧ p5))))) → p3) ∨ False)) ∨ ((p2 ∧ p2) ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158254985848731674615672925720 : ((((True ∨ p3) → p2) ∨ (p2 → ((((p1 ∨ (p3 ∨ p4)) → (p3 ∨ True)) ∨ True) → (p5 ∨ p4)))) ∨ ((p4 ∧ ((False ∧ False) ∨ p5)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301866475659497262453934640935 : (False ∨ ((p2 → p3) ∨ (((((p1 → False) ∨ (p1 → (p2 ∨ (True ∨ (p3 → True))))) → p1) → (p1 ∨ ((p4 ∧ (True ∨ True)) ∨ p2))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → False) ∨ (p1 → (p2 ∨ (True ∨ (p3 → True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14869411085483537139089609237 : (((((p3 ∧ (p3 → (p2 ∨ (p5 ∧ p4)))) ∨ p4) ∨ (True ∨ ((p5 ∧ (p2 → True)) ∧ (((p5 ∧ p3) ∨ True) ∧ p5)))) ∨ (False ∧ True)) ∧ True) := by
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
theorem thm_5_vars_716503483434275042333645357491 : (((((False ∨ True) ∨ (p3 → p1)) ∧ (p5 ∨ ((p5 ∨ (p5 ∧ True)) ∨ ((((p2 ∨ p3) ∧ (p3 → p1)) ∨ p2) ∨ (p4 → (False ∨ True)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153559980989532482587841781179 : ((True → (True → (False ∧ (False ∨ (p1 → ((True ∨ ((p4 ∨ p4) → ((p1 → p1) → (p5 ∧ p1)))) ∧ p3)))))) → (((False ∧ p5) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607065190495222998950110962003 : (((((((p4 ∨ (p1 → p5)) ∨ ((p3 ∨ (p2 ∨ p2)) ∧ p2)) ∧ ((p4 ∧ (True → ((False → (False ∧ False)) ∨ p2))) → p2)) ∧ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217594635742166186315916644624 : ((((True → False) ∨ p4) → False) → ((((p2 → (p5 → p3)) ∧ p5) ∨ ((True ∧ (p1 ∨ (((False ∨ False) ∧ p5) ∨ (p2 ∧ p5)))) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218122638226468012873672034833 : (((p2 → p3) ∧ (p4 ∨ p2)) → (p2 ∨ (True → ((((p5 → p5) ∨ ((p5 ∨ p4) → ((p2 ∧ p2) ∧ p1))) → (p1 ∧ (p3 ∧ True))) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319658125403554063935961205799 : (p4 ∨ ((p5 → ((p4 ∨ ((p3 ∧ p1) ∧ p3)) ∨ p5)) ∨ ((((True ∧ (p5 ∨ p5)) → p3) → (p2 → (p4 ∨ p5))) → (p1 → (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722956463607642162000265085979 : (((((p5 ∧ p3) ∨ p5) ∧ ((((p4 ∨ (p4 ∧ p2)) ∧ (p1 ∧ (p1 → (False ∧ False)))) ∧ p4) ∨ ((((p3 ∨ p5) ∧ p5) ∧ p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_989460573018851398014542660003 : (((p3 ∧ (((p2 ∨ (p2 ∧ p1)) → False) ∧ (p3 → ((((p2 ∧ (p1 ∨ p1)) → (True ∨ (p4 ∨ (False ∧ True)))) ∨ False) ∧ (p4 ∧ p5))))) → p4) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157579266652962132397383644938 : ((((False ∧ p3) → (True → (((((True ∨ p1) ∨ p3) ∧ p3) ∧ (p1 ∨ p1)) → p1))) → (p4 ∧ p2)) ∨ (True ∧ ((p3 ∧ p5) → (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234069000719149990278080486728 : ((True → (False ∧ True)) → ((p1 ∨ ((p4 ∨ (False → ((((p3 ∧ ((p5 → p2) ∨ True)) ∨ p4) → p3) ∨ False))) → (p2 ∧ (p1 → p3)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868248468322355017034547605048 : (((((p2 ∨ p2) → ((((p5 → (p4 ∨ (p1 ∨ p2))) ∨ p1) → (p5 ∨ (p4 → (p3 → (False → p4))))) ∨ (p2 → (p4 ∧ p1)))) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ p2) → ((((p5 → (p4 ∨ (p1 ∨ p2))) ∨ p1) → (p5 ∨ (p4 → (p3 → (False → p4))))) ∨ (p2 → (p4 ∧ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- False on the left can always be used.
        apply False.elim h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150016722349622294942391938924 : ((p5 ∨ ((False → (p1 ∨ (((True ∧ p5) → True) → ((p5 ∨ p1) ∧ (p2 ∧ p3))))) ∧ ((True ∧ False) ∨ p4))) ∨ (p1 ∨ (p5 ∨ (p2 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348213316291798989854589330745 : (p3 → ((p2 → False) → (p5 → (p1 → (((p3 ∧ (((p4 ∧ (False → False)) ∨ (p3 → p1)) → (p2 ∧ p3))) ∨ ((False → False) → p1)) ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179431695639002598944578680933 : ((p4 ∨ (p4 ∧ (((p2 ∧ p4) ∧ p1) → ((p4 ∨ (p3 ∧ p1)) → p5)))) ∨ (((p5 ∨ p3) → p3) ∨ (p2 → ((p3 → p4) → (False ∨ True))))) := by
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
theorem thm_5_vars_209285188819697499578803773377 : ((True → ((p3 ∧ (p5 → False)) → p5)) → ((p5 ∨ p4) → (((((p3 → p5) → p3) → p1) ∧ False) ∨ (p5 ∨ ((True ∨ (True → True)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116783188736156273452926387015 : (((p1 ∨ p1) ∨ ((p4 ∨ (True ∧ ((p1 ∧ (((False → p1) ∧ False) → ((p4 ∧ (p3 ∧ p1)) → (False ∨ True)))) ∧ p4))) → False)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316393041381530173865217822651 : (p3 ∨ (False ∨ (((p2 ∧ p5) ∨ (p2 ∧ (True ∨ p1))) → ((p1 ∨ (True ∧ (p4 ∧ False))) ∨ ((True ∧ True) ∨ (((p3 → True) ∧ p3) → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149134289898757275389219742254 : (((p4 ∧ False) ∧ ((p3 ∧ (((p2 → True) ∧ ((False ∧ p5) ∨ p5)) ∨ True)) → (p4 ∧ ((p2 ∧ p2) → False)))) ∨ (p5 → (True → (True ∨ True)))) := by
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
theorem thm_5_vars_217992580799765641437617369096 : (((p4 ∧ p4) ∧ (p5 → p5)) → (((p5 ∧ (((False ∨ p3) → (((False → p1) → p1) ∨ p2)) ∧ (p1 ∧ ((p1 ∧ False) ∧ p5)))) ∨ p3) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147154648531776686636232527137 : (((p3 ∧ (((True ∨ (False → p3)) ∧ True) ∧ (p4 ∨ ((p4 ∨ ((True ∧ (p2 ∨ p2)) → p2)) ∨ True)))) ∧ p2) ∨ ((p1 ∨ (True ∨ p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_315191603549245272276365181598 : (p3 ∨ (((True → (p1 → True)) ∨ False) ∧ (((((False ∧ p1) ∨ p3) ∧ (False ∧ ((p3 → True) → (p2 ∧ p4)))) ∨ (p1 ∧ p3)) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157914527319868631812245284209 : ((((p2 → p4) → (((p4 ∧ p2) ∧ False) ∨ (p2 → p4))) → (False ∧ (False ∨ (p5 ∨ (p1 ∧ p2))))) ∨ (True ∨ (False → ((p5 → p3) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357170195608222262500281056645 : (p5 → ((True ∨ p4) ∧ (p3 → ((p2 ∨ (p4 ∧ ((p5 ∧ p1) ∧ (p3 → (p2 → p4))))) ∨ (p1 ∨ ((((p2 ∨ p4) ∨ p3) ∧ True) ∧ p5)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342471688489243620798962797865 : (p2 → (((((((p5 → p2) ∨ ((False ∨ p1) → p3)) ∨ True) ∧ p3) → p1) ∧ False) ∨ ((False ∨ (True ∨ p3)) ∨ (p5 ∨ (True ∧ (p3 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65850172077817586178968695246 : ((p4 ∨ (((p1 ∧ p2) ∨ p1) → ((p4 ∨ (((p1 → False) ∧ False) → p5)) → (((False → p5) → (p3 ∧ p4)) → (True ∧ (p5 → p4)))))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h14
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48752526268371918358168038516 : ((((False ∨ False) ∧ ((False ∧ (((p4 ∨ p5) → ((p1 ∧ (p1 ∧ p2)) ∧ p1)) ∨ ((p3 → False) ∧ p2))) ∨ True)) ∧ (p3 ∨ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134372789424971769559942040770 : (((p2 ∨ (p5 ∨ ((True ∨ ((p5 → p4) → (((p2 → (p2 ∧ p1)) → (p3 ∧ (p5 ∧ p1))) → p5))) ∧ p2))) ∨ p5) ∨ ((p1 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255439517927818092460432794893 : ((p5 ∧ p1) → (((False ∧ p3) ∧ (p5 ∧ ((((False → ((p3 ∨ p2) → p3)) → p4) ∨ (p4 → p5)) ∧ (p2 → p5)))) ∨ (p1 → (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245354548167812869578228392033 : ((p2 ∧ p3) ∨ ((((((((p2 ∨ False) → p3) ∨ p4) ∨ p3) ∧ False) ∨ p4) ∨ ((False → (((False ∧ p2) ∨ p4) ∨ p3)) → p5)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961395312659005490309217522222 : ((((p2 ∨ p2) ∧ ((p1 ∨ True) → ((True ∨ ((((p1 ∨ p1) → (p4 ∧ (p5 ∨ p1))) → True) ∧ (True ∨ ((p3 ∧ p3) ∧ p4)))) ∧ False))) → p5) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319273336670918654322157870546 : (p4 ∨ ((((((p2 ∧ (p1 ∨ (p2 → p5))) → True) → False) ∧ False) ∧ ((True ∨ p3) ∨ p2)) ∨ (True ∨ ((((p2 ∨ p3) ∨ p1) ∨ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230474773290501013546887051147 : (((p5 ∨ p4) ∧ p4) → (p2 ∨ ((True → ((p4 → (p2 ∧ (p5 → ((True → p4) ∨ True)))) ∨ p5)) ∨ ((True ∨ (p4 ∧ p5)) ∧ (True ∨ p3))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190953866194037027196734530657 : (((p5 ∧ (False ∨ (False → True))) ∧ (p1 ∨ (p4 → p2))) ∨ (p4 → ((((p5 ∨ True) ∧ p2) → (p3 ∨ p4)) ∨ (p5 → (p4 ∨ (p3 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320262723109202655398716090376 : (p4 ∨ ((True ∧ p2) ∨ ((True ∨ p2) → (((False → ((p4 ∨ p3) ∨ p3)) ∧ p3) ∨ (((p4 → p3) ∧ p2) ∨ ((p2 → (p1 → True)) ∧ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713537279952873197892061537 : (((True ∧ ((True → p2) ∧ ((p1 ∧ p4) ∧ True))) ∨ (p3 ∧ (p2 → (((False ∨ (p4 → False)) → ((p1 ∨ p5) → p3)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329539534750029634775224999385 : (True → ((p4 ∧ p5) ∨ (p1 → (((p1 → False) ∧ p3) → (False ∧ (((True ∨ p3) ∧ p1) ∧ ((p1 ∨ p4) → ((True ∧ p3) ∧ (p1 → p5))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h3.left
    let h22 := h3.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h23 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h3.left
    let h27 := h3.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h28 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h29 := h26 h28
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117363142945974687443940700885 : ((False ∧ (p2 ∨ ((p3 → (p5 ∧ False)) ∨ ((True → (((p5 → p1) ∨ ((True ∨ p4) ∨ p4)) → p2)) → (False ∨ (True ∧ p4)))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58169888331058489766544575658 : (((p3 ∧ p1) ∧ ((True → ((False ∨ ((((False → p1) ∧ False) ∨ ((p1 ∨ (True → False)) ∧ ((p2 ∨ p5) ∧ p1))) ∨ p3)) ∨ False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_369924439467330231290477935649 : ((((((((p3 ∨ (False → p4)) → p1) ∧ p4) ∧ p4) → (((p3 ∧ (((p2 ∧ True) ∧ (p2 ∨ (p4 ∨ p2))) ∨ p1)) → p5) ∨ p1)) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141186615473061948273440321164 : ((((p3 ∧ (False ∨ (p3 ∧ p3))) → p5) ∨ (((((((p5 ∨ p5) ∧ True) ∧ True) ∨ p1) ∨ p5) ∧ p3) → (p4 ∨ True))) → ((p5 ∨ True) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177628950377252562831784331741 : (((((p3 → (((p2 ∨ True) → p4) ∧ (p1 → p5))) ∨ p3) ∧ p1) ∧ p2) ∨ ((p3 → False) → ((p5 → (((p5 ∧ p1) ∧ p2) ∨ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117443535895389166060616709094 : ((p1 ∧ ((p3 ∧ ((p5 ∨ (p5 → p5)) ∨ p5)) ∧ (((((p3 → ((False ∧ (p5 ∨ False)) → True)) → p5) ∧ p5) ∧ p3) ∨ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



