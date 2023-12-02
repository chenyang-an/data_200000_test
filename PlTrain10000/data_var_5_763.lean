variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39713267243268177770051694301 : (((p5 ∨ ((p2 ∧ ((False ∧ ((True ∨ p2) ∧ p4)) ∨ (p4 ∧ (((((p2 ∧ p5) ∧ p5) → p5) ∨ (p4 ∧ p5)) ∨ p2)))) ∨ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116253519614610429184554403780 : (((True ∧ (p4 ∧ False)) ∨ (((True ∧ p5) ∨ (False ∧ p2)) ∨ ((p5 ∨ True) ∧ (True ∧ ((True ∧ p3) ∨ (p1 ∨ (p2 ∨ True))))))) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192828659467689616659803390715 : (((p5 → (p5 ∧ ((True → (p4 → True)) → p2))) → p2) → (((False ∧ ((((False ∧ p3) ∧ p4) ∨ p4) ∨ p4)) ∨ (True → p1)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114565746359317834950076417766 : (((((((True → p5) → ((p3 → p3) → True)) → p1) ∧ (False ∨ True)) ∧ (p5 ∧ False)) ∧ (((p5 → (p4 → p2)) → p3) ∨ False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798521186260580047840208279247 : (((p1 → (((False ∨ p1) ∧ (((p4 ∨ p5) ∧ p2) ∨ p4)) ∨ ((p2 → (p2 → p4)) → (p4 → (p2 → (((p3 ∧ p3) ∨ False) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716444037142021313826982320606 : (((((p5 → p5) ∧ (p5 ∨ True)) ∧ ((((p5 ∨ p4) ∧ (False ∨ p2)) ∨ (((False ∧ (p2 → ((True ∨ p1) ∨ p4))) → p3) ∨ p5)) ∨ False)) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185842468291586030629737234235 : (((((p3 ∨ (p3 → ((p5 ∨ p5) ∧ p1))) ∨ p2) ∨ p3) ∧ p1) → ((((False ∧ p1) → p4) ∧ p1) → ((p3 → True) → (p4 → (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210385282687298228944206939754 : (((False ∨ (p5 ∨ True)) ∨ p1) ∧ ((((((True ∨ (p1 ∧ ((True ∨ (p5 ∧ p2)) ∨ ((p2 → p3) ∨ p3)))) ∧ p5) → False) ∨ p5) ∨ False) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258446071457168822777193834318 : ((p5 ∨ p1) → (p4 ∨ (((((((p3 ∨ p2) → p5) → p4) ∧ p2) ∨ (p3 ∨ p2)) ∧ ((p1 → False) → True)) → (False ∨ (p3 ∨ (False → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323386059768904641385707953131 : (p5 ∨ ((p3 ∨ (((p5 → p1) ∧ p4) → (True ∧ (((True → (p3 → p4)) → False) ∧ ((p5 → p5) ∧ ((True ∧ p3) ∨ p2)))))) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186147599157800318679983148921 : ((((p1 ∧ p5) ∧ (((p1 ∨ (True ∨ p5)) → p1) → p3)) ∨ p5) → ((((p4 → p1) ∧ ((p4 ∨ p1) ∧ (p4 → p1))) ∨ (False → p5)) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808997025148545479966365420929 : (((p5 → (((((p4 ∧ p3) ∧ p4) ∨ p1) ∨ (p3 ∨ (True → (p1 ∨ ((p3 → (False ∧ (p3 ∧ p4))) ∨ (p2 → (p5 ∨ p2))))))) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47507496910403619629385157715 : (((p2 ∨ (((p2 ∧ ((((True ∨ (p3 ∧ p3)) → p5) → (((p2 ∨ p4) ∨ False) ∧ p5)) ∧ (p5 ∧ True))) → p2) → p5)) ∨ (False → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724514829593699728561225454514 : ((((False ∨ (p1 ∨ True)) ∧ (p2 ∧ (((((((p4 → True) → True) ∨ True) → p5) ∨ (p5 → p1)) → p2) → (p4 → ((p2 ∧ p3) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37444302849973985540557057579 : (((((p4 → ((p4 ∨ ((p5 ∧ False) → (p5 ∨ p2))) → ((p3 ∨ p2) ∨ p5))) ∧ (((True ∨ p5) → (p2 → False)) ∧ p5)) ∨ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641505466401725086885012551374 : (((((p1 ∧ False) → ((((p1 ∨ (((p5 → p2) → (False ∧ p5)) ∧ ((False ∧ (p1 ∨ p4)) ∨ p5))) → True) → (p2 ∧ p5)) → p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351683228745549819324063442713 : (p4 → ((p4 ∨ ((p3 ∨ ((((p1 ∧ True) → (True ∨ p4)) → False) ∧ True)) ∨ (p4 ∨ p4))) → (((False → p1) → ((p2 ∨ True) ∧ p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : ((p1 ∧ True) → (True ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h12
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113685818412326014142925055729 : (((((p3 ∧ (((p5 ∨ ((p1 → ((True ∨ p4) ∧ False)) ∧ (p2 ∨ True))) → p3) ∧ (p4 → p2))) ∨ p1) → p1) → (p2 ∧ p5)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654612105982613150974562222010 : (((((p1 → (p4 ∨ ((True ∨ ((p2 ∨ ((p1 ∨ p1) → p3)) ∧ ((False ∧ p5) ∨ ((p1 ∧ p4) → p4)))) ∧ p3))) ∨ False) ∨ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137818289790106751983755844156 : ((p3 ∨ (((True ∧ (p3 ∧ p1)) ∨ (p4 ∨ (p5 → (p2 ∨ (False ∨ (p2 ∨ ((True ∨ (p2 → p2)) ∨ p5))))))) ∨ p3)) ∨ ((p2 → True) → False)) := by
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
theorem thm_5_vars_314843156359461591002323717453 : (p3 ∨ ((p1 ∧ (((((p5 → (p3 ∧ False)) → True) → p5) ∧ p5) ∧ True)) ∨ ((p3 → (p3 ∨ (p5 ∧ (True ∧ (p2 ∧ p5))))) → (True ∨ p1)))) := by
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
theorem thm_5_vars_942796912520780680155961502635 : (((((p2 → (True → True)) → False) ∧ (p1 ∨ (p3 → ((((True ∧ (p4 → True)) ∨ (p5 ∧ False)) ∨ True) ∨ ((False ∧ (p5 ∨ p2)) → p3))))) → p3) ∧ True) := by
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
    have h5 : (p2 → (True → True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p2 → (True → True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h10
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742802581086661701377390257065 : ((((p3 → p1) ∨ ((((((p1 ∧ False) ∧ (False → p3)) → ((p5 → False) → p1)) ∨ ((p5 ∨ (p2 ∨ p4)) ∨ p2)) ∨ p3) → (p5 ∨ True))) ∨ p3) ∧ True) := by
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
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745319028304710705085523898433 : ((((p5 ∧ p2) → ((p3 ∨ ((p4 ∧ ((False ∨ (p4 ∧ p2)) ∧ (p5 → ((True → (p2 ∨ p3)) ∧ (p5 → (True → p3)))))) ∧ p1)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_484514249178482515619110220219 : (((((p2 → False) → (True → (False ∨ True))) ∧ ((True → ((p5 → (p5 ∧ (((p5 → False) ∧ (False ∧ p4)) → (p3 ∨ p5)))) → p1)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304739979970677236465969841135 : (p1 ∨ (((p3 ∨ ((p2 ∧ p5) ∧ p5)) ∧ ((p2 → p2) → (((False ∧ False) → ((p3 ∨ p4) ∨ False)) → ((True ∨ p3) → p3)))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613920129584289131810340481340 : ((((((False ∧ ((p4 ∨ p1) ∨ (True → (p2 ∧ ((True ∨ p4) ∧ (p5 ∨ (p5 → False))))))) ∧ (p4 ∨ p2)) ∨ ((p5 ∧ p3) → p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185794846037897684441087845037 : ((p5 → ((True → (True ∧ ((False → True) → (False → p1)))) → False)) ∨ ((p1 → False) → ((p4 → False) → ((p5 → (p1 ∨ p1)) ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_214422463180228244197952582870 : (((p2 → (p4 → p2)) → p1) ∨ ((False ∧ p5) ∨ (((p2 ∧ p4) ∧ (p3 ∧ True)) ∨ (((p2 ∨ False) ∨ ((p2 ∨ p4) ∧ p5)) → (p3 → p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178725657499608189771027814882 : (((((p5 → True) ∨ p3) → p4) → (False ∨ (p5 ∧ (p4 ∧ (p3 → p4))))) ∨ ((((False ∨ ((False → p2) ∨ False)) → True) → True) ∨ (True → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114680688315553643286419056615 : (((False ∨ ((((p3 ∧ (p1 ∧ True)) → ((p5 → p1) ∨ (p2 → True))) → p3) → p5)) ∨ ((False ∧ p3) ∧ ((p4 → p1) ∨ p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224477530020882351682402851596 : ((p1 → (p2 → p1)) ∧ (((False ∨ ((p1 → (p5 → p3)) ∧ ((((p5 ∨ p5) ∧ True) ∨ ((p2 → p5) → p3)) → False))) → (True → p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_465622144970824562754540922681 : ((((((((False ∧ ((p4 ∧ p1) ∨ (False → False))) → p4) ∧ p2) ∨ p2) ∨ True) ∧ (((p2 ∨ (p1 ∨ p2)) ∨ (p3 → p3)) ∨ (p1 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253141692211621461217835718527 : ((True ∧ p5) → ((p3 ∨ (p1 → ((p4 ∨ (p3 ∨ True)) → False))) → ((p4 ∨ ((False ∨ False) ∨ ((p2 → False) ∨ (True ∧ (p5 ∨ p2))))) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158858953651522920611235654483 : ((False ∨ ((True ∧ (True → ((p5 ∨ (p2 ∨ (((p3 ∧ p3) ∧ p3) ∨ True))) ∨ (p1 ∨ p2)))) ∨ p4)) ∨ ((p3 ∨ p5) → ((p2 ∨ p2) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_49244169209567899639277172527 : ((((True → p3) → (((p2 → (p1 → (False ∨ (p3 ∧ ((p2 ∨ False) → p3))))) ∨ (False → p4)) → (p5 → p2))) ∨ ((p1 → p2) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307284459768514967926121746318 : (p1 ∨ (p2 ∨ (False ∨ (((((((p2 ∧ (p4 → ((p4 ∧ p3) → p1))) → p3) ∨ False) ∧ (p5 → (False ∨ p5))) ∨ True) ∨ (p3 ∨ p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114552125812268905639036086600 : ((((((False ∨ p4) ∧ (((p4 ∨ (False → (p1 ∧ p1))) ∨ p5) ∧ p1)) → p4) ∨ p3) ∧ ((((p4 ∨ p2) ∧ p1) → p2) → False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192466250877448415139094068048 : ((((p4 ∧ (p1 ∧ (True ∧ p5))) ∨ (True ∧ p4)) ∨ False) → (((p3 → (p5 ∧ p4)) ∨ p3) ∨ (((p5 ∨ p1) → (p3 ∧ p1)) ∨ (p4 ∨ p4)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355562523542718409203936879172 : (p5 → ((((((((p5 → p2) ∨ ((((p5 → p3) ∨ False) ∧ True) → p2)) → p4) ∧ (p4 ∨ p4)) → False) ∨ p2) ∨ (p5 ∨ p2)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598086227958726576893504004604 : (((((p4 → (p5 ∧ p4)) ∧ (((p3 ∧ p2) ∨ False) ∨ (p1 ∨ ((p3 ∨ ((((p3 → p2) → p2) → p1) → (p5 ∧ p1))) ∧ p1)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172979296955710848957193769818 : ((p4 ∧ (False ∨ (p3 ∨ ((p5 → ((((p1 ∧ p3) ∨ p2) ∧ p4) ∨ False)) → p1)))) ∨ (((((p3 ∧ p1) ∨ p4) ∨ (p4 ∨ p5)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761366385943945115408890507041 : (((p3 ∧ ((((p3 ∨ (p4 → False)) ∧ (((False → p3) ∧ p5) ∨ p4)) → (((((p1 ∨ True) ∨ p2) ∧ True) ∨ p1) ∧ (False ∨ p5))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249518241736782469668163916648 : ((p5 ∨ p1) ∨ (p3 ∨ (True ∧ ((((p5 → (True ∨ p4)) ∧ p5) → ((False ∧ (p1 → (p5 → False))) ∧ p1)) ∨ ((p4 → (p4 ∨ p3)) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52322694377655019159026679487 : (((((False ∨ (p2 ∨ p3)) → ((p2 ∨ (p3 ∨ (p5 → p3))) ∨ p3)) ∨ p5) ∧ (True → (p5 ∧ ((((True → p2) → p2) ∧ p3) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43263735347521610418902231113 : ((((p3 → (((p4 ∧ False) → (p5 ∧ (p3 → (False ∧ (p1 ∧ False))))) ∨ (False ∧ (True ∧ ((p3 → p4) ∧ (p1 ∧ True)))))) ∧ p2) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149140376753657748292721873169 : (((p5 ∧ p3) ∧ ((((((False ∨ p1) ∧ (p1 ∨ True)) → (True ∧ True)) → p2) ∧ (p5 ∧ (p5 → p4))) ∧ p2)) ∨ (p4 → (p4 ∨ (False → p1)))) := by
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
theorem thm_5_vars_764922564007697264434872966961 : (((p4 ∧ ((((p2 ∨ p4) ∨ False) ∨ ((((True → p3) → p3) ∨ p1) ∧ ((True ∨ (p3 ∧ ((p5 → p5) ∨ (p3 → p3)))) ∧ True))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223981119221173396945730540477 : ((p4 ∨ (p5 ∨ True)) ∧ ((p2 ∧ (((((p2 ∧ True) ∧ (p1 ∨ p4)) → (True → p1)) ∧ (True ∧ (p3 ∧ (p4 → p5)))) → (p5 → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1765932447430181743864108263 : (((((p2 → ((False ∨ p5) ∨ p3)) → ((p4 ∨ (p5 ∧ p1)) ∧ (True ∨ False))) ∨ (True → (p1 → p2))) ∨ p2) ∨ (False → (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263547271305129286141584424687 : (True ∧ ((((((((False ∨ ((p2 ∧ p4) ∧ True)) → (p3 → p3)) ∨ p3) → (p4 → p4)) → p1) → p5) ∧ p4) ∨ (((p3 ∨ False) ∧ False) → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328535302955955539603205818107 : (True → ((p3 ∨ (p2 ∨ ((p1 ∧ (p3 ∨ (False ∧ (False ∧ p5)))) ∧ (False ∧ (p2 → p5))))) ∨ ((p1 ∨ (p5 ∨ (p2 → (p4 ∨ True)))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228097099045860831898073747132 : ((p4 ∧ (p1 ∨ p5)) ∨ (p4 → (p3 → (((True ∧ (((p2 ∨ p4) ∨ (False ∧ p5)) → p5)) ∧ (p5 ∨ (p3 → (False → False)))) ∨ (p3 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_688584632934003942412649753786 : ((((p2 ∨ (p4 → (((p5 ∧ False) ∧ ((p2 ∨ (p2 ∨ (p2 ∨ p1))) → p2)) → True))) ∧ (p2 ∨ ((p3 ∧ ((True → False) ∨ p4)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165524084073591240670174005588 : ((((p3 ∨ p1) ∨ ((True → (False ∨ (p3 → True))) → p3)) → (p2 ∨ ((False ∨ p1) ∧ p5))) ∨ (p3 ∨ ((p2 ∨ (False ∧ False)) → (False ∨ True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308550310302406970188619324789 : (p2 ∨ (((((True ∨ False) ∧ p2) ∨ ((p1 ∧ p2) ∨ p5)) ∧ ((((p3 ∧ True) → (p5 ∨ ((False ∧ (False ∧ False)) ∧ p4))) → p3) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301400054908495616409573820737 : (False ∨ ((p1 → ((p4 → True) ∧ p4)) ∨ (((((p1 → p4) → False) ∨ p2) ∧ (False ∨ (p4 → (p3 → ((p2 ∨ (False → p4)) ∨ True))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60771200789595911682233514050 : ((True ∧ ((p3 ∨ p5) ∨ (((p2 ∧ ((True ∨ ((True ∨ (p4 ∨ (p3 ∧ p2))) → p1)) ∨ ((True → p3) → False))) ∨ (p3 ∧ p5)) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172038804621854805578926881651 : (((p2 ∨ ((False ∨ False) ∨ ((p4 ∧ (p1 ∨ (p3 ∧ p3))) ∧ True))) ∨ (p3 → p2)) ∨ (True → ((p2 → False) ∨ (p3 ∨ (p2 ∨ (True ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_157214979287606806634929149025 : ((((((p5 → True) ∧ (False → False)) ∨ ((False ∨ (p4 ∧ False)) → p2)) ∧ ((p5 → p5) ∧ p1)) → p5) ∨ (True ∨ (True ∨ ((p4 → p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178207060566126721383568728946 : (((p2 ∨ ((p3 ∨ (((p4 ∨ p4) ∧ False) ∨ p4)) ∨ (True → p3))) → False) ∨ ((True → (((p3 → (p3 → p4)) ∨ (p4 ∨ p4)) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689371158561384976979170632330 : (((((((((False ∨ p3) ∧ (True ∧ p2)) ∧ p4) → (p2 → p5)) ∧ p2) → (p1 ∨ p3)) ∨ (False → ((p5 ∧ (p1 ∨ (True ∨ p5))) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139039085963223152532212632931 : ((((((p1 ∧ (((False ∨ (p5 → p4)) ∧ p2) ∧ p2)) ∧ (p1 → p3)) → ((p1 ∧ (p5 → False)) ∧ p2)) → p3) ∨ p4) → ((p4 → p2) ∨ True)) := by
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
theorem thm_5_vars_184270739023935863021063722134 : (((((((p4 ∧ True) ∨ p3) → p1) ∨ p3) → (p3 → p1)) → p5) ∨ (p2 ∨ ((p5 → p2) ∨ (((p4 ∨ True) ∧ p2) → (p4 → (p4 ∨ p4)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156824392376294824686066467933 : (((p5 ∨ (((p4 → (((p5 ∨ p4) ∧ (p4 ∨ (p1 ∨ p3))) → True)) → (p5 ∧ p5)) ∧ True)) ∧ p1) ∨ ((p3 → p3) ∨ ((False ∧ p2) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46887133758390766703110898881 : ((((((((p1 ∨ p4) → (((True ∨ True) → (p3 ∧ p5)) ∨ (True ∨ p4))) ∨ p1) → (p3 ∧ (p4 → p2))) ∨ False) ∨ p2) ∨ (p2 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42338588785702091334069093292 : (((p3 ∧ ((p5 ∧ ((False ∨ (p4 → False)) ∧ (p5 ∧ ((p1 ∨ (((False ∧ p1) ∧ p5) ∨ (False ∧ (p3 → p5)))) → p3)))) → p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262215230786041864460576486263 : (True ∧ ((((((p1 ∧ (p4 → p3)) ∧ (((True ∨ p5) → p1) ∧ (p4 ∨ (p4 ∧ False)))) ∨ ((p3 → p2) → p3)) ∧ p1) ∧ (p3 → p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351326194450373506641674964761 : (p4 → ((False ∨ ((p5 ∧ (((p1 ∧ (p5 ∨ p4)) ∧ ((True → ((p5 ∨ p4) ∨ p3)) → True)) ∧ p5)) ∧ (p4 ∨ p4))) → ((False ∧ False) ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200335498938942396422631566022 : (((p2 ∨ p1) ∧ (p2 → ((p2 ∧ p4) ∧ p4))) → (((p1 → p4) ∧ (p3 ∧ p5)) ∨ (True ∨ ((True ∧ p5) ∨ ((p2 ∧ (p2 ∧ p2)) ∧ p1))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38608503276719602278097561180 : ((((((False → p2) ∨ p3) → ((p2 ∨ p2) ∨ p2)) ∧ ((((p1 ∨ p5) ∧ p1) → (p2 → (p1 ∨ (p5 ∨ (p3 ∨ p3))))) ∧ p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633317480818284220309782610522 : ((((((p5 ∨ (((p2 ∧ p5) ∨ p4) ∨ ((((p2 ∧ p4) ∨ (p1 → p1)) ∨ False) ∨ (p1 ∨ (p4 ∨ p3))))) ∧ p5) ∨ (p1 → p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160019495041344723797616007684 : ((((p4 ∧ (p4 → p2)) ∨ (p5 ∨ ((p3 ∧ (p5 → (True ∨ (p5 ∧ (True ∧ p2))))) ∧ False))) → p5) → ((p3 ∨ ((True ∧ p1) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178316784863132819039945050975 : (((((((p2 → (p4 ∨ p3)) ∧ p3) ∧ p4) → p1) → p3) ∨ (p5 ∨ p2)) ∨ (((False → p4) ∧ p4) → ((((True ∧ p5) ∧ False) → True) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694661634628805972069035389848 : ((((False ∨ ((((p5 ∨ p2) → p1) ∧ (((p5 → p5) ∧ True) ∨ True)) → p4)) ∨ ((((p2 ∨ p1) → p4) ∧ (p2 ∨ (True ∨ True))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41980409709709503938012102328 : ((((p3 ∨ False) ∧ ((p4 ∧ (p2 ∧ (((p5 → p1) ∨ True) ∧ (((False ∧ ((p2 ∨ False) → p5)) → False) ∨ (p1 ∨ p2))))) ∨ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346295126968340578505783631622 : (p3 → (((((((p1 ∨ (False ∧ p3)) → (p4 ∧ p1)) ∧ (((True ∨ p3) ∧ p1) → p3)) → p5) ∨ (p3 ∨ (p1 ∨ p2))) ∨ p4) ∨ (p3 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206123800481261887155823044256 : ((p4 ∧ ((p4 ∧ p1) ∨ (p2 ∧ p5))) ∨ ((((p1 ∧ p2) → (p2 ∨ (((True ∨ p4) ∨ ((p3 → (False → p1)) → p3)) ∧ p4))) ∨ p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686581367478749322586753887392 : (((((p5 → False) ∧ ((((p2 ∨ p5) → (p2 → p1)) ∨ (p5 → (False → p4))) → (p4 → p3))) → ((((p2 ∨ p3) ∧ p3) ∧ p2) ∨ True)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697177675827538249368580911117 : (((((p4 ∧ (p4 ∨ p2)) ∧ ((p3 ∧ p2) ∨ ((p4 ∧ p2) → p5))) ∧ ((p1 ∨ ((((True ∨ p5) → p4) ∧ True) ∨ (p2 ∨ p3))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149110629133846062485022927811 : (((p5 → (p5 ∨ True)) → (p5 ∧ (p5 ∧ (True ∧ ((True → ((p5 → (p3 ∧ (p4 ∨ p3))) ∨ p4)) ∧ p2))))) ∨ ((p3 ∧ (p1 ∧ False)) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165367139905753933698275662669 : ((((((p1 ∧ p5) ∨ (False ∧ ((p5 ∨ p3) ∨ p4))) ∧ False) ∨ p1) ∨ ((True ∨ p2) ∨ p2)) ∨ (p4 → (p5 → (p2 ∨ (p1 → (p1 ∧ p3)))))) := by
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
theorem thm_5_vars_45427135454084091567838018110 : (((True ∨ ((((((p5 ∨ p4) ∧ (p2 ∧ (((p4 ∨ p1) ∧ (p5 ∧ p1)) ∧ p2))) → p1) ∨ p5) ∧ (p2 → (p1 → p1))) ∨ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654162001837019496201553300051 : (((((((p4 ∨ (((((p2 ∨ p5) ∧ (p2 → p4)) ∧ True) ∨ ((p4 → p1) ∨ p1)) → (p5 ∨ p1))) ∨ True) ∨ p3) ∨ p5) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16880863517218517101654219781 : ((((p3 ∨ p1) → ((((False ∨ (p1 → p2)) → p3) → (False ∧ ((True ∧ (p1 ∨ (True ∨ p5))) ∨ p2))) ∧ p5)) ∨ (False → (True ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185295713274551732478113652462 : ((p2 ∧ ((False → True) → ((True ∨ True) ∧ ((p2 → p1) → False)))) ∨ ((((p4 → (p2 → True)) → ((False ∧ (True ∧ p3)) ∧ p5)) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710163159194804556545514878892 : (((((((False ∧ p4) ∨ p4) → p5) ∨ p3) ∧ (((False ∧ (((False ∧ (((p4 → (p2 ∧ p5)) ∧ p4) → True)) ∨ p2) ∧ p2)) ∨ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65209444885918231892845585055 : ((p3 ∨ (((p3 ∧ (p5 ∨ (((p2 ∨ True) ∧ ((p1 ∨ p5) ∨ p2)) ∨ ((p4 ∧ (True ∨ p3)) → (p1 → p3))))) → (p5 → p4)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134783683307369682220170031664 : (((p1 ∧ ((p2 ∨ ((p5 ∨ p3) ∧ (True → p3))) → (False → (((True → (p2 ∧ (p2 → True))) ∧ p5) → p1)))) → p2) ∨ ((p3 → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49886765717636352999635279572 : (((((False ∧ ((p4 → ((p4 → (p5 ∧ p2)) ∧ True)) ∧ True)) ∨ (p2 → ((False ∨ p5) ∨ p3))) ∨ True) ∧ (False ∧ ((False ∧ p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136735875195336878781795708030 : (((True ∨ p3) ∧ ((((p5 ∨ p5) → p1) → ((((p3 ∨ p3) ∨ False) → ((True ∨ True) ∧ p5)) ∧ p5)) ∨ (p3 ∧ p2))) ∨ ((p2 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158708232963252543915942727324 : ((p3 ∧ (((p4 → (p2 → ((p3 ∨ (p3 ∨ (p4 ∨ p1))) ∨ (p3 → p5)))) → (p5 ∧ p1)) ∨ p2)) ∨ ((p3 → p2) → (p5 → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255528406088450652265485804909 : ((p5 ∧ p2) → (p1 ∨ (((p2 → (p4 ∨ ((False ∧ p3) → p1))) ∧ ((((p4 → p1) ∧ p4) ∧ ((p4 ∧ p4) ∨ True)) ∨ (True ∧ p4))) ∨ p5))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114701891179238766483038886242 : ((((((p5 → (p1 ∧ (((p5 → (p2 → p3)) → p1) ∧ p5))) → p2) ∧ True) ∨ True) → ((p5 ∨ (p5 ∧ False)) ∧ (p1 ∨ True))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186470610612168897563053510017 : ((((p5 → (p3 ∧ (p2 ∧ p3))) ∧ (p4 ∨ p5)) ∧ (p2 → p1)) → (p4 ∨ ((p2 → p4) → ((False ∨ (p2 ∧ ((p3 ∨ p2) → p3))) → p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157783277220631208193849599646 : ((((((p1 ∧ (p5 ∧ (True → True))) → False) ∨ p2) → (p2 → p1)) ∨ (((p5 ∧ p1) ∧ False) ∨ p3)) ∨ (((True ∨ True) ∨ p1) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136164945460238128597300856103 : (((False → (p5 ∨ ((p5 ∨ p3) ∧ (p1 → p3)))) → ((p3 ∨ p1) ∧ ((p5 → ((p4 → False) ∧ (p5 ∧ p5))) → False))) ∨ (p3 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52179097696120994715446705529 : (((((p1 ∧ False) → (p5 ∧ (p4 ∧ p3))) → ((p3 ∨ False) ∧ ((False → p2) ∨ p4))) → ((((p4 ∧ p1) → p4) ∧ (p4 ∧ p2)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313978836135836967709718422887 : (p3 ∨ (((p2 ∨ ((((p1 → p3) → p1) ∧ p1) ∨ (p1 ∧ False))) → (p3 → ((p4 → (p5 ∨ ((p1 ∧ p4) → p5))) ∨ False))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156595212794982417521396587032 : ((((((False ∨ ((p5 → p5) ∧ p5)) ∧ ((p5 ∧ True) → ((p1 ∧ True) ∧ False))) ∨ False) ∧ p3) ∧ p4) ∨ ((True → p1) → (True ∨ (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



