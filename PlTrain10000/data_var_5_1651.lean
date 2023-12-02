variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205813786909711637203180626787 : (((p4 ∨ p1) → (False ∧ (True ∧ False))) ∨ ((p1 ∧ ((((p5 → p5) → p4) → p3) ∧ p3)) → ((True ∧ (p2 → (False ∨ False))) ∨ (p2 → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116019370028999835661870448266 : (((True ∧ ((p1 → False) ∧ p2)) → ((p4 ∨ False) ∧ (((p4 ∧ (p3 → ((p1 ∧ p2) ∧ p5))) → (True → (True ∧ p1))) ∧ False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702244853723330259393401546784 : ((((((p1 → (p4 ∧ True)) ∧ ((p4 → False) ∧ p4)) ∧ p2) ∨ ((p5 ∨ (((False ∨ (p5 → (p3 ∨ p1))) → (p1 ∧ p4)) ∨ p5)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_350138126468489459184823846402 : (p4 → (((p4 → ((False ∨ p3) → (((p1 → p2) ∧ p2) → ((True ∨ p3) → False)))) → ((p3 ∨ ((True → p5) ∧ (p1 ∧ True))) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_791216978451296245089710784 : (((p1 → p1) → (((p1 ∧ (False → ((((p5 → p1) ∧ False) ∨ (p4 → False)) ∨ p3))) ∨ (p3 → ((p3 → p5) ∨ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47607442786557373545978423117 : (((p4 → ((p5 → ((True ∨ ((p3 → False) ∨ ((p1 ∨ p2) ∧ (p3 ∧ ((p3 ∧ p4) → (p1 ∨ p5)))))) ∨ p3)) → False)) ∨ (p5 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190394603384920048338523405405 : (((p1 ∧ (p3 ∨ (p4 → ((True → p3) ∨ False)))) ∨ False) ∨ ((((False → p5) → ((p5 → True) → p5)) → ((True → False) ∨ (p1 → True))) ∨ p4)) := by
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
theorem thm_5_vars_58396796191459472945423872944 : (((p2 ∨ True) ∧ ((((p5 → p5) ∨ (False → p4)) ∧ (True → False)) → (((p3 → (False ∧ (False ∧ True))) → False) ∨ ((p3 ∨ p5) ∨ p5)))) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113057195621459180014122583356 : (((p2 ∨ (((p4 → p5) ∨ ((((((True → p2) ∧ ((True ∧ p3) ∧ p5)) → (True ∨ True)) → p2) → True) ∧ False)) → p1)) → p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172009173257652091081044577924 : (((((((p2 → True) → (True → p1)) → True) ∨ p3) → (p4 ∧ False)) ∨ (True ∨ p4)) ∨ (p2 ∨ (((p1 → p2) ∧ p5) → ((p2 → p3) → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178870098182715462839866688411 : (((True ∧ p1) ∧ ((p1 → (p4 ∧ True)) → (((p3 → p1) ∧ True) ∧ p4))) ∨ ((True → False) ∨ ((p2 ∨ (((p5 → p5) ∧ False) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184518377848868256881509258666 : (((False ∨ ((p1 → p1) ∧ ((p5 ∨ p4) → p1))) ∨ (p1 ∧ p3)) ∨ (False → (False ∧ ((p2 ∨ ((p4 ∧ (p3 ∨ p5)) ∨ (p3 ∨ p4))) ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204445088807362130078215302207 : (((((p4 ∧ p3) → p1) ∧ p4) ∨ p3) ∨ ((((p5 ∧ False) ∨ (p4 → ((p2 ∨ (False → (p4 ∨ p2))) ∧ (False ∨ p5)))) ∧ p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113965453911301250725358988257 : (((False ∧ ((((True ∧ (p4 → (True ∧ p4))) ∧ (p2 → p2)) ∧ (p1 → ((False ∧ True) ∨ False))) ∨ p3)) ∧ ((p2 → p3) ∨ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809909165765416416401256399138 : (((p5 → ((((((p2 ∨ (p3 ∧ p5)) → ((False → p5) ∨ False)) ∧ ((False ∨ p3) ∧ p2)) ∨ p4) ∧ (False → p1)) ∧ ((p3 ∨ p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673886990550217808299947196689 : (((((False ∨ p1) → ((p1 ∧ True) ∧ ((p4 ∨ (p3 ∧ ((True → (p5 → p5)) → (p3 → p2)))) ∧ (p3 ∧ p5)))) → (True → (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114883366717877542448803852062 : ((((p3 → p4) → (p3 ∧ ((p5 ∧ False) → (p3 → (False ∧ (p5 ∧ True)))))) ∨ ((p5 → ((True → p5) ∨ (p5 → True))) → p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46134941158949748501111020074 : (((((((p1 ∨ ((p1 ∨ False) ∧ (False → (True ∨ (p3 → (p4 ∨ ((True ∧ True) → p5))))))) → p5) ∧ p3) ∨ p2) → p4) ∧ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157961990851510416748711854901 : (((((p1 → (p2 ∧ p2)) → p1) ∨ (p2 ∨ p3)) ∨ (((p3 ∨ p5) ∧ ((p4 ∨ p4) → False)) ∧ p1)) ∨ (True ∨ (((False → p4) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644321025849608154869465032074 : ((((False ∨ ((False ∧ (p2 ∧ (p1 ∧ ((p1 ∧ p5) ∨ (((True ∧ p5) ∨ p2) ∧ False))))) → (((p3 ∨ p1) ∧ p2) ∨ (p4 → p4)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328420270903962105374268390540 : (True → (((p5 → ((p2 → p4) ∧ p1)) ∧ (p3 ∨ ((p3 ∨ (p1 ∧ (p2 → (p2 ∧ False)))) → p3))) ∨ ((p4 ∧ ((False ∧ False) ∧ p5)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114620799224740233426434864585 : ((((((False → (False ∧ (((False → p2) ∨ p2) → False))) → p4) ∧ (p2 ∧ p2)) ∧ p1) ∨ (p2 → ((p2 ∧ (p5 → p5)) ∧ p5))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631066497722465574741103493529 : ((((((((((True → (p5 ∧ False)) ∨ ((p5 ∨ True) ∧ p5)) → p3) ∧ p3) → ((p1 ∧ ((p3 ∧ False) ∨ p1)) → False)) ∨ p1) → p1) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786168810032145115093049884716 : (((p4 ∨ ((p4 ∧ (p5 → ((((((False ∧ ((p2 → p3) → p4)) → (p3 → p5)) ∨ True) ∧ p1) ∨ p2) ∧ True))) ∨ (p5 → (False ∨ p5)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96395297896367311532093306374 : ((False ∨ ((((p5 ∨ (p4 ∧ (((False → (False ∨ p5)) → p3) ∧ (False → (p4 → p2))))) ∧ True) ∨ (p1 ∧ p5)) ∧ (True → (p5 ∧ False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h19 := h5 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792327836310966545266126371796 : (((True → ((((((p2 ∧ p3) ∨ (p5 ∨ p5)) ∨ p5) ∨ p1) ∧ (((p2 ∧ p5) → p3) ∧ p2)) → (False ∨ ((p2 ∨ p1) → (True → p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h4.left
        let h11 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h4.left
          let h19 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- One of the premise coincides with the conclusion.
            exact h19
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h4.left
          let h26 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- Implications on the right can always be decomposed.
          intro h28
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h30 =>
            -- One of the premise coincides with the conclusion.
            exact h26
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h4.left
      let h33 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h34
      -- Implications on the right can always be decomposed.
      intro h35
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- One of the premise coincides with the conclusion.
        exact h36
      case inr h37 =>
        -- One of the premise coincides with the conclusion.
        exact h33
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h4.left
    let h40 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h41
    -- Implications on the right can always be decomposed.
    intro h42
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h43 =>
      -- One of the premise coincides with the conclusion.
      exact h43
    case inr h44 =>
      -- One of the premise coincides with the conclusion.
      exact h40
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192633258606369153485703876370 : (((((False → ((True ∧ True) ∧ True)) ∨ p3) ∨ p3) → True) → (p2 ∨ (p4 → (((False → (True → (p5 ∧ p2))) → (p2 ∧ (p1 → p2))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157518072662221468882610609655 : (((p3 ∨ (p4 ∧ ((False ∨ p5) ∧ (p3 → (False ∨ (p1 → ((p3 ∧ p5) ∧ p4))))))) ∨ (True → p5)) ∨ ((True ∨ ((p4 → p1) ∧ p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205458253181995331934750596397 : (((False → (p4 ∨ True)) → (p2 ∨ p2)) ∨ ((True → ((True → (True → (False → p5))) → p1)) → (((True ∧ (True ∨ (p5 ∨ True))) ∧ p1) → p1))) := by
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
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159035388212497346069960465781 : ((p4 ∨ (p4 ∨ (p2 ∧ ((((p5 → (p3 ∨ p5)) ∨ p1) ∧ (p5 ∨ (p5 → (p3 ∨ False)))) ∨ p4)))) ∨ ((p3 → True) ∨ ((p1 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67589478773114676866422170068 : ((p1 → (True ∧ (((((False → p2) → (False ∧ (False ∨ p4))) → (p4 ∧ ((p3 ∨ p4) ∧ p1))) ∧ (p2 ∧ ((p5 ∧ p1) ∧ False))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57923181226639636337969238745 : (((True → (True ∧ False)) → (False ∨ (((p5 → p3) ∨ ((p3 ∧ (((((p4 ∧ (p2 → p2)) ∨ p4) ∨ p5) ∧ p5) → False)) → p3)) → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208957872952609177505478660792 : ((True ∨ ((p2 ∧ (p1 ∧ p5)) → p5)) → (p4 ∨ (p5 ∨ (p4 ∨ ((p5 ∨ (((False → p5) ∨ (p2 ∧ (p5 → p5))) ∨ (p3 ∨ False))) ∨ p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19906708887169360649413360662 : (((True → ((((p4 → p2) ∨ (((True ∨ p3) ∨ p1) ∧ p3)) ∨ p4) ∧ (False ∧ True))) → (((p2 ∧ p4) ∨ ((True ∧ p1) ∨ p3)) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78824635613527052147334863321 : ((((True ∨ (p2 → (p2 → False))) → ((((((p4 ∧ p2) → (False ∨ p5)) → (p5 ∨ p5)) → p3) ∨ True) ∧ (p3 ∧ p5))) ∧ (True → p4)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p2 → (p2 → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136993844346050445773779292479 : (((True ∨ True) → (((((((p1 ∨ p2) ∨ p3) ∨ (p3 ∨ (p3 → (p2 → p4)))) ∨ (p4 → True)) ∧ p1) → p4) → p1)) ∨ (p1 ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207632263411765045799516043438 : ((((p4 → (p5 ∨ p5)) → p2) → p2) → (((False ∨ (p4 ∧ (((p1 ∨ p4) ∨ (True ∨ p4)) → True))) ∨ (False → True)) → ((p5 → p2) ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66512822681172455427723827272 : ((True → ((((p5 ∨ p3) → (p4 ∨ ((p2 ∨ ((((p3 → False) ∨ False) → p5) ∨ p3)) → ((p5 → (p2 ∧ False)) ∧ p2)))) ∧ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179228408474709713388344437405 : ((p4 ∧ (p1 ∨ ((((p3 ∧ ((p1 ∧ p1) ∨ p3)) ∧ False) → p3) ∧ p2))) ∨ (p3 ∨ (p3 ∨ ((((p3 ∨ p2) ∧ p5) → (p2 → p5)) ∨ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259383584708062094506858476621 : ((False → p3) → ((p4 ∧ ((((p5 ∧ p1) → ((False → ((p1 → ((True → p3) → p2)) → p5)) → False)) ∨ (True ∨ p3)) → p3)) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42998986736178638461694548948 : (((((((False ∨ True) ∧ (False → (True ∧ (p5 ∧ ((p1 ∨ p5) ∨ ((((p4 ∨ p1) ∧ p4) ∨ p3) ∨ p4)))))) ∧ p3) ∧ p3) ∧ p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185240311268300769024624327465 : ((False ∧ (p1 ∨ ((p4 ∧ (p5 ∨ p3)) ∧ ((p4 ∧ p1) ∨ p4)))) ∨ (False → (p2 ∨ ((False ∧ True) → (((False ∨ p3) ∨ p1) ∨ (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248864963392480969080689646070 : ((p3 ∨ p5) ∨ ((((True → False) ∨ ((((p5 ∧ (p3 ∧ p4)) ∨ True) ∧ ((p2 ∧ ((p2 ∧ False) ∧ False)) ∨ p5)) → False)) ∧ (p4 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322253952326015226516900954824 : (p5 ∨ ((((p1 → ((p2 → ((True → p3) → ((p1 → (p2 ∧ p2)) ∧ p4))) ∧ False)) → (p4 ∧ ((p3 ∧ (True → p5)) → False))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51179302233777961734024319584 : ((((((p4 ∧ False) → False) ∨ ((p4 ∨ p2) ∧ (((p4 ∨ True) ∨ True) ∨ p1))) → (False ∧ False)) ∨ (((p5 ∨ (True ∨ True)) → p5) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52610547517078410913901617807 : ((((p2 ∨ ((p4 ∨ p1) → False)) ∨ ((p4 → True) → ((False → p2) ∧ p1))) ∨ ((((p2 ∧ p5) → p1) ∨ p5) ∨ ((p2 → p1) → True))) ∨ p1) := by
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
theorem thm_5_vars_254042423979864074803137628819 : ((p2 ∧ True) → (((p4 → (p3 ∧ (((((True ∨ p4) ∧ (p1 → (False → p2))) → False) ∨ (False → p5)) → p2))) → p1) ∨ (p3 ∨ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133613205745892969910818308580 : (((((p3 → (False ∨ ((p2 ∧ p4) ∧ (p4 → (((p2 → p1) ∨ (p2 ∧ p3)) ∧ p1))))) → (p5 ∧ p3)) → p4) ∧ p1) ∨ ((p3 → p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180696756354092112334579250335 : (((((True → p5) ∧ p5) ∧ p1) ∧ (p1 ∧ (True ∧ (p3 ∨ (p1 ∨ p4))))) → (p1 ∧ ((p1 → p4) ∨ (((p5 → (True ∨ p5)) ∨ p2) → p1)))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h17.left
  let h23 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h27
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h34 =>
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h35 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h36
      -- One of the premise coincides with the conclusion.
      exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164758220036983766793414743915 : ((((p4 ∨ (((p4 ∨ False) ∧ (p1 ∨ True)) ∧ (False ∧ p2))) ∧ ((p5 ∧ p5) ∧ p4)) ∨ p2) ∨ ((p5 ∨ ((False ∧ p1) → (False → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1970894604598418919565541247 : ((p1 ∧ (((p2 ∨ ((p3 ∧ (p1 ∧ (p3 ∨ (p3 ∨ (p3 ∨ False))))) → True)) → (p1 ∧ p5)) ∧ False)) ∨ (False → (True → (p4 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178353507939113013742601864668 : (((p1 ∨ ((((True ∨ p3) → (True → p5)) → True) ∧ p4)) ∨ (False ∧ p1)) ∨ (((p2 ∧ p4) ∧ (((p4 ∨ p2) ∧ True) → False)) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148985655482712477975737379612 : (((True ∨ (p4 ∨ p2)) ∧ (p3 → (((p2 ∧ (True ∨ p3)) ∨ p2) ∨ (((p1 ∧ (p4 ∧ p5)) → p5) ∧ p5)))) ∨ (p1 ∨ (False ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_173316668484843872480817088463 : ((p2 → ((False ∧ ((p1 → (((p4 ∨ p3) ∨ p2) → (p1 ∧ False))) ∧ p4)) ∧ True)) ∨ (p4 ∨ ((p2 ∧ ((p5 ∧ p2) → (p3 → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197719239897776842517652298711 : ((((False → p1) ∧ False) ∧ ((p2 ∧ True) ∨ False)) ∨ ((((True ∧ True) ∧ p4) ∨ p1) → (p4 ∨ (((False → p3) → ((p5 ∧ p2) ∨ p3)) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443727857669503274121962545845 : ((((((True ∨ (True ∧ p4)) ∨ p2) → ((p2 ∨ (((False → p4) ∨ True) ∨ (False ∧ False))) ∧ (p2 → (p4 ∧ False)))) ∨ ((True ∨ p2) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606470203285483597287451189616 : ((((((p3 → (True → (p4 → (False ∧ ((((False ∨ p3) ∧ (p3 → (p1 ∨ (p4 ∧ p3)))) ∨ True) → (p4 → p1)))))) ∨ p4) ∧ p5) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_194021172578181138796833250711 : ((p4 ∨ (p1 ∧ (p3 ∨ (False → (False → (False ∨ True)))))) → ((((True ∧ ((p1 ∨ ((p5 ∨ p3) ∨ True)) ∨ p5)) ∨ (p4 → False)) → p4) ∨ p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h12 =>
              -- One of the premise coincides with the conclusion.
              exact h2
          case inr h13 =>
            -- One of the premise coincides with the conclusion.
            exact h2
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55559606381236677031587440277 : (((p4 ∧ ((p1 ∨ (True ∨ True)) ∧ p3)) → (False ∧ (((p2 ∨ False) ∨ ((p4 ∨ (((p4 ∧ False) → True) → p3)) → p1)) → (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310416813443467078174754463779 : (p2 ∨ ((((p2 ∨ (True ∧ (p1 → p3))) ∨ p1) ∨ p1) → (p4 ∨ ((p4 ∨ (True → (True ∨ (False ∨ p5)))) ∨ (((False → p4) → p5) ∨ p4))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230147267645103241387663109131 : (((p4 ∧ p2) ∧ p3) → ((True ∧ ((((p2 → (p3 ∨ (p3 → p1))) ∧ ((p5 ∧ p3) → True)) → (p1 → ((p3 → p3) ∨ p1))) → p5)) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113143121056874292083189852750 : (((p3 → (((p5 ∧ (((True → p5) ∨ p1) ∨ p1)) ∧ (((False → True) ∨ True) → ((p1 ∧ p2) ∨ (True → True)))) ∧ p4)) → p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54757266150174425187205044182 : ((((p4 ∨ p5) ∨ (True → ((True ∧ p2) ∧ p4))) → ((p1 → ((False → ((True ∨ ((False → p1) ∧ (p4 ∨ p5))) → p1)) → p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241664569614727887481741774747 : ((False → p5) ∧ (((p3 → (p1 ∨ p4)) ∧ (p5 ∧ p4)) ∨ ((p1 ∨ (p1 ∨ True)) ∨ ((p5 ∨ p5) ∨ ((p3 ∨ p2) → ((p2 ∧ p5) ∧ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47641630118996180638055541801 : ((((((((((((p3 → p3) ∧ (True ∧ p5)) ∨ True) ∨ p4) ∧ (True → p3)) ∧ (False → p1)) ∧ p1) ∨ p1) → p3) ∧ p1) → (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258796748453603133267415453631 : ((True → False) → ((p5 ∨ p2) ∧ ((p3 ∨ ((False ∧ (p2 → p5)) ∨ ((((True ∧ ((False → p2) ∧ p5)) → (True ∨ True)) ∨ p4) ∧ p5))) ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722329890935784222317656918040 : (((((p2 ∧ p1) ∧ p1) ∧ (((p1 → False) ∧ (False ∨ p2)) → (p2 → (p5 ∧ ((p5 → False) → (p1 → ((False ∨ (p4 ∧ p2)) ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53098385927291581548001125446 : (((p4 ∨ (((p5 ∨ ((p4 ∨ True) ∨ False)) ∨ p5) → (p5 ∨ p5))) ∧ (((((True → p1) ∨ (p3 ∨ p2)) → True) ∨ True) → (True → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325914585684135575934177917133 : (p5 ∨ (p5 ∨ (((p3 → (p5 ∨ ((p5 ∨ False) ∧ ((True ∨ (((p1 → p3) ∨ True) ∨ (p5 → False))) ∧ ((False ∨ p5) → p4))))) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212272437972213041883809111917 : ((False ∨ (p4 → (p4 → p4))) ∧ ((((p2 ∨ p3) → ((p1 ∨ p4) ∨ True)) ∧ p1) → ((False ∨ ((p3 ∧ p2) ∧ (p3 ∧ (p2 ∨ p4)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191740870645345730305904042854 : ((False ∨ (((p5 ∧ p2) ∨ p2) ∧ (p4 ∧ (p1 ∧ False)))) ∨ ((p2 ∨ p1) → ((((True ∧ p2) ∨ (True ∨ (True → p1))) ∧ False) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_249472929794609935243655555835 : ((p5 ∨ p1) ∨ (((((p3 ∨ (p1 → p3)) ∨ ((p1 ∧ True) ∧ (((p4 → p5) → p1) ∧ p3))) ∨ True) ∨ (p5 → (p5 → (p1 ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657830243011339164855431243236 : ((((False ∧ (((p3 ∨ (p4 ∨ (p4 ∧ p5))) → ((p5 → (p2 ∨ p5)) ∨ ((p2 → (p3 ∨ True)) ∨ p1))) ∨ (False ∧ True))) ∨ (p2 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_302785279626082005971065184610 : (False ∨ (p4 ∨ (p3 ∨ (((((False ∧ ((p3 ∨ p2) ∨ True)) ∨ (p4 → ((p3 → (True ∨ p4)) → (p2 ∧ p4)))) ∧ True) ∧ (p1 ∧ p5)) ∨ True)))) := by
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
theorem thm_5_vars_149992733556851166269474169501 : ((p4 ∨ (p3 ∨ (((p1 → (p5 ∨ (p3 ∧ (p1 → p3)))) → (p5 ∨ False)) ∨ ((p4 ∨ p2) ∨ (p2 ∧ p3))))) ∨ ((p4 ∨ (p4 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49223233776153036774695894891 : ((((True ∧ p1) ∨ ((p5 ∨ ((((p5 ∧ True) ∨ p2) → (((p2 → p3) ∧ p3) ∧ False)) → p2)) ∨ (p4 → True))) ∨ (p3 → (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626967205041354111582464711153 : ((((((((p1 → ((p3 → p3) ∧ (False ∧ ((p3 ∨ p2) ∧ (((False ∧ p1) ∨ p5) ∨ (p4 ∧ False)))))) → False) ∨ p2) ∧ p3) ∧ p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132822696256192400207888197949 : ((p2 ∨ (((p4 ∨ True) ∧ p3) ∨ ((p2 ∧ ((False ∨ p1) ∧ ((p1 ∨ (p5 ∨ p3)) ∧ (p3 → p4)))) ∨ (p4 ∨ True)))) ∧ (p5 → (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118548239989448456576736138948 : ((p3 ∨ (p5 ∨ (((p2 ∨ (((p4 ∨ (p1 ∨ p4)) ∨ p1) ∧ (p3 → (((p5 ∨ p3) → p5) → p4)))) ∨ p5) ∨ (p4 → p5)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110929373775942088871110575146 : ((((((((((True ∧ False) ∨ True) ∧ ((p4 → p3) ∨ ((True → p5) ∨ p2))) ∨ p5) ∧ p2) ∧ p1) ∨ True) ∧ (False ∨ p5)) ∧ p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46263980427589188463576002976 : ((((True ∧ (((p2 ∧ (False ∨ p3)) → p3) → (((((p2 → p4) → True) ∧ (False ∨ p2)) → True) ∨ False))) → (p4 ∧ p4)) ∧ (False → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157224198959382227669103906757 : (((((p5 ∨ (p2 ∨ False)) ∨ ((p3 ∧ p2) ∨ ((p4 ∧ p3) ∧ True))) → ((p1 ∨ p4) → p2)) → p2) ∨ ((p4 → (p2 ∧ p3)) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191082253630469674123605426202 : ((((p4 ∨ p4) ∧ True) ∧ (p1 ∧ (True → (p1 ∧ p2)))) ∨ (True ∧ ((((p1 ∨ p1) ∨ (True → (p2 ∨ ((p5 ∨ p5) → p4)))) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52394759448323641752077900288 : (((((p1 → (True ∧ True)) ∧ p5) ∧ ((p5 ∧ ((False ∧ p4) ∨ p4)) → p2)) ∧ (p4 ∨ (((p2 ∨ p4) ∧ p2) ∧ ((True ∨ p3) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199767218825008472952542951627 : (((p2 → ((p3 ∨ (False ∨ p1)) ∧ p2)) → True) → (((p4 → ((False → p4) ∨ p2)) → False) → ((p5 ∧ ((p2 ∨ p4) ∧ p1)) ∧ (p4 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → ((False → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → ((False → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h7
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (p4 → ((False → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h11
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h15 : (p4 → ((False → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h18 := h2 h15
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h19 : (p4 → ((False → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h21
    -- False on the left can always be used.
    apply False.elim h21
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h22 := h2 h19
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318194429212419729358706699955 : (p4 ∨ ((((p1 → p4) ∧ ((((p2 ∧ (p3 ∨ p1)) ∨ p4) ∨ p5) ∧ (True → p5))) ∧ ((((p5 ∨ True) ∨ (p1 → p1)) ∨ p3) → p3)) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h14 := h7 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h17 := h7 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h20 := h7 h19
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54596380709002258133202861705 : (((True → (p2 → ((p5 ∧ (p1 ∧ p1)) ∨ False))) ∨ (p2 ∨ ((p4 ∧ ((p5 → True) → False)) ∨ (p2 ∨ (p4 → ((True → False) → p3)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335701801845085088622776277972 : (p1 → ((((p2 ∧ (p4 → ((p1 ∧ p5) ∨ p5))) → ((p4 → (False ∧ (False → (p1 → True)))) ∨ (((True ∨ p2) ∧ False) ∨ False))) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230798265497314226818153659130 : (((False ∧ True) ∨ p1) → ((p1 → ((p1 ∨ True) → (True → False))) → (p2 ∨ ((p5 ∧ (((p5 ∨ p5) ∧ ((p1 → p5) ∨ p5)) ∨ p3)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350181509614661354568731537599 : (p4 → ((((True → (False → p1)) ∧ p3) ∨ ((((p4 ∧ (p2 → True)) ∨ True) → ((p2 ∨ (p3 ∨ (p3 ∧ p5))) ∨ (p5 → p5))) ∨ p5)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641120598850684488660105153613 : (((((False ∨ False) ∨ (((p5 ∨ p4) ∨ ((((p4 ∧ p4) ∨ False) → p1) ∨ (p2 → p3))) ∨ ((((p3 → False) ∨ False) ∧ False) → p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44340181130153774553066329216 : ((((((p5 ∧ p3) → ((p4 ∧ False) ∧ (p1 ∧ (p5 ∨ p1)))) ∧ (p3 ∧ (p2 ∧ p5))) → (((p2 ∧ (p2 ∨ True)) → p1) ∧ False)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113753799463955016318582688019 : ((((p5 ∧ (((p5 → False) → ((p2 → p1) ∨ p4)) ∨ p3)) → (False ∨ (False ∨ (((p1 ∧ p4) ∨ False) ∧ p1)))) → (p4 ∨ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326859783861474775901352062213 : (True → (((((p3 → ((((True ∧ True) ∨ (False → ((((False ∧ p2) ∧ p2) ∧ p3) → (False ∨ p3)))) ∨ p5) ∧ p2)) → p2) ∧ p3) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205109612576593756814740322778 : ((((p3 ∧ p5) ∨ p2) ∧ (p5 ∧ p2)) ∨ (p3 → (((p1 ∨ True) ∨ (p1 ∨ (((p2 ∨ p3) ∧ (((p2 → False) ∨ p5) ∧ False)) → False))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974510829580926919827899175151 : ((((p1 → True) → (True → ((p1 ∧ ((True → (False ∧ ((((p4 ∧ p1) ∧ p4) ∧ p3) → p3))) ∧ ((p2 ∨ p2) ∨ (p5 → p4)))) ∨ p3))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
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
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h15 := h10 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h19 := h10 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h23 := h10 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114104547490326632339946175193 : (((p4 ∧ (p4 ∧ ((p5 ∨ p4) ∨ ((((p5 → (p5 ∧ p2)) → p2) ∧ (p1 → (p3 → False))) ∨ p1)))) ∨ ((p2 → p2) ∨ p1)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109334600773223561802902296293 : ((p1 ∨ (((((False ∧ ((p2 ∨ p3) ∧ False)) ∧ True) ∧ (True ∧ p3)) ∧ p4) ∨ ((((p5 ∨ (False ∨ p3)) ∧ p3) → p3) ∨ p1))) ∧ (p2 → True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198719153940538738258607143918 : ((p5 ∨ ((p1 → (p4 → p5)) → (p2 ∧ p2))) ∨ ((((p1 → p1) ∨ (True ∨ p1)) → ((p2 ∧ p4) → ((p1 → p1) ∧ p4))) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39042402867710055854041273874 : ((((True ∧ p2) ∨ ((p5 → (((False ∨ (((p5 ∧ p1) → p3) → p1)) ∨ (((p5 → False) ∧ p4) ∨ p1)) ∧ (p5 → p5))) ∧ p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



