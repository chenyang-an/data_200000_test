variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656115474311803485560033736101 : ((((((((p3 ∧ (p5 ∧ False)) → p1) → p4) ∨ (p4 ∨ ((p3 → False) ∧ p4))) ∧ ((True → p3) ∧ ((p5 → p1) → False))) ∨ (p2 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305891424483868455876004663271 : (p1 ∨ ((p4 ∨ (p5 ∨ (p5 ∧ (True → p4)))) ∨ (False → (((False → False) → p4) ∨ ((p1 → (True ∨ p3)) → (p5 → ((True ∨ p1) ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622808316377080416472450973181 : ((((p4 ∧ (p4 → (p2 ∨ ((p2 ∧ (p2 → (p4 ∧ True))) ∧ (p1 ∧ ((p5 ∨ (p4 ∨ (p5 ∨ (False ∧ True)))) → (p3 ∨ True))))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116830476403988198610511869970 : (((p5 ∨ p3) ∨ ((p3 ∨ ((((True ∧ p3) ∨ (((False ∧ p3) → (p5 ∧ p1)) ∧ False)) ∧ p5) → (p2 ∨ False))) ∧ (p5 ∧ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717967644746668706500581269827 : (((((p5 → (p4 ∨ p1)) ∧ p1) ∨ ((False ∨ (True → (True ∧ ((((True ∨ False) → ((p3 → True) ∧ p4)) ∨ False) ∨ p1)))) → (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658499918243218064208540240014 : ((((p2 ∨ (((((p2 ∧ False) ∨ p3) ∧ ((((p4 → False) → (p5 ∧ (p4 ∨ p2))) ∨ (p5 → p4)) ∧ False)) ∧ p1) ∧ p2)) ∨ (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114801350639155311281085864151 : ((((((p4 ∨ (True ∧ p1)) ∧ p4) ∨ p4) ∨ ((False ∧ (False ∨ p4)) → True)) ∧ (p4 ∨ (p2 → ((p4 ∧ (p2 ∧ False)) → p1)))) ∨ (p1 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690443074238418846170575697269 : ((((((p3 ∨ (p1 ∧ (p3 → (((False ∨ False) ∨ True) ∧ (p5 ∧ p5))))) → p4) ∧ p2) → (((((p2 ∨ False) ∧ True) → True) → False) ∨ p2)) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171301240988566649581998895002 : (((((p3 → (((False → p5) → p2) ∨ False)) ∧ (p3 ∧ (p2 ∧ p2))) ∧ p3) ∧ p4) ∨ (p2 → (((True ∨ p2) ∨ p1) ∨ (p1 ∨ (False → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147648330548122980614162138236 : ((((p5 → (p2 ∨ ((p4 → False) ∧ ((p2 ∧ (p1 ∧ (p5 ∧ True))) → (p3 ∨ (p1 ∧ p4)))))) → True) → p1) ∨ ((False → True) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330438899333510106649453281302 : (True → (p3 ∨ (((p4 → (p5 ∧ (False ∨ p3))) ∧ ((p2 → True) → ((True → False) ∧ False))) → (((False ∧ True) ∨ ((p2 → p3) → False)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234624200535649757362923683206 : ((p3 → (False → p4)) → (((p1 ∨ (p2 ∧ ((p1 ∨ (False ∨ False)) ∧ (p4 ∨ False)))) ∧ (((True ∧ p1) ∧ (p5 ∨ p3)) → True)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_114020751459407468169544428383 : (((((p2 ∧ (p2 ∧ p5)) ∨ ((True ∧ p3) ∧ ((p2 ∨ False) ∨ ((True ∧ p2) ∨ (p2 ∧ False))))) ∨ p2) ∨ (p4 ∨ (p5 ∨ True))) ∨ (True → p4)) := by
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
theorem thm_5_vars_148795434101028223535648989062 : (((p4 → (True → ((p3 → True) → p3))) ∨ ((((p1 → p4) → ((p4 → (p1 → True)) → False)) → False) ∨ p5)) ∨ (False → (p4 ∨ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174583405476223082590785201340 : ((((p1 → (True → True)) ∧ p3) ∨ (((True ∧ (p3 ∨ p4)) → (p5 ∧ False)) ∧ p4)) → (((True ∧ (False → p1)) → ((p3 ∨ p2) ∧ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (True ∧ (p3 ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48493996298067110627607387260 : ((((p1 → ((p4 ∧ p5) ∧ ((p3 ∧ p5) ∨ ((p3 → p4) → (((p3 ∧ p3) ∧ p3) ∧ (p1 → True)))))) ∧ p4) ∧ (p5 → (True ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39623856742127958274153301353 : (((p2 ∨ (p4 ∨ (p5 → ((p3 ∨ (p3 ∨ p3)) → ((p1 ∨ p4) ∧ (p1 ∨ (p4 ∧ (p1 ∧ (((True ∨ p4) → p5) → True))))))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41626806069546291409878539589 : ((((((p2 ∨ p1) → (p2 ∧ p1)) → (p4 → p5)) → ((p4 → True) ∧ ((((p5 ∧ p4) ∨ (p2 → p5)) ∨ p3) ∧ (p5 ∧ p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197046872397993318650169828246 : ((((p1 → True) ∧ ((p2 ∧ p3) ∧ p1)) ∨ p1) ∨ ((((p3 ∨ p3) ∨ (p5 → (p5 ∨ False))) → (((p5 → False) ∨ (False ∨ p4)) ∧ p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p3) ∨ (p5 → (p5 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112919407617048060460686737527 : ((((p3 → True) ∨ (p4 ∨ (((p4 → p5) ∨ (p2 ∨ ((p4 → (p3 ∨ (p3 ∨ p2))) ∨ (p2 ∧ p2)))) ∧ (p4 → p3)))) → p1) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51056979003171851012560959226 : (((p5 ∨ (((p5 ∨ ((p4 ∨ p3) → (False → (p1 ∧ True)))) ∨ False) ∧ (p3 ∧ (True → p4)))) ∧ (p1 ∨ ((p3 → (p1 ∧ p5)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317050102030111645209088876822 : (p3 ∨ (p4 → ((p5 → (((((p4 ∨ (p2 ∨ (p2 → p4))) ∧ p5) → p2) ∧ p2) ∨ (((p2 ∧ True) → p5) ∨ p4))) ∨ (True → (False → p5))))) := by
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
theorem thm_5_vars_822299941920920448135350642463 : (((((((True ∧ (p5 → p5)) ∨ p4) → ((True ∧ p4) ∧ p4)) ∧ ((((p1 ∧ p4) → (p1 ∧ (p4 → p1))) → p5) ∨ (False → p2))) ∧ True) → p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∧ (p5 → p5)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : ((True ∧ (p5 → p5)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172709471952180905834936798136 : (((p2 ∨ p1) ∨ ((((True → p2) ∨ (p2 ∨ (p3 ∧ p2))) ∨ p4) ∨ (p4 → True))) ∨ ((((True → ((True ∧ p3) → p1)) → p4) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256763501190943718621852279684 : ((p1 ∨ p2) → ((p2 → ((p3 ∨ ((((True → p2) ∨ ((p1 ∨ ((False ∨ p2) ∧ p1)) ∧ p1)) ∧ p4) ∧ p3)) → ((p3 ∧ p5) ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
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
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h38 =>
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353888943459011177698870616136 : (p4 → (p1 → (p5 → ((((p5 ∧ ((p2 ∨ (((p1 ∨ p1) ∨ p5) → p2)) ∨ (True → (p1 → p5)))) → ((True ∧ p3) ∨ p2)) → p3) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694879582112261299456531242239 : ((((p3 → ((p3 ∧ p5) ∨ (((p1 ∨ p1) ∨ False) ∧ ((p4 ∨ True) → p2)))) ∨ ((p3 ∧ (p1 ∧ (p4 ∨ p1))) ∨ (p2 ∨ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712638552426729081278163655442 : (((((p1 ∧ p1) ∧ ((p4 ∨ p4) ∨ p1)) ∨ (p1 ∨ (((p3 ∨ ((False ∨ ((True ∨ ((p2 ∧ False) → p5)) → p4)) ∨ True)) ∨ p3) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245585287258588927348374526599 : ((p3 ∧ False) ∨ ((((p4 ∧ p4) ∨ (p5 ∨ (((p4 ∧ ((p1 ∧ (p3 ∨ p5)) ∨ (p5 → False))) → (p5 ∨ p4)) → (p1 ∨ False)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156676166665558707688161382259 : (((((((p4 ∧ False) → (p5 ∨ (p5 → ((True ∨ p1) ∨ p2)))) ∧ p1) → p5) ∨ (p3 → p4)) ∧ False) ∨ (((p2 → (p4 → p5)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303089617458746954512715783671 : (False ∨ (p2 → (p3 ∨ (p4 → (((False → True) ∨ ((((False ∧ p3) ∨ (p1 → p5)) → (False → p1)) ∧ (p5 ∨ (True ∨ p5)))) → (p1 ∨ p2)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205810323243735744903597063307 : (((p3 ∨ p4) → (p4 ∧ (p3 ∨ p1))) ∨ (((p3 → p1) ∨ p2) → ((((((False ∨ p2) → False) → (p2 → p2)) ∧ (p5 ∨ p4)) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43255721589505830129601944375 : ((((p1 → ((p5 ∨ ((False ∨ (((p5 ∧ (p2 → True)) ∨ (True → p3)) ∨ p5)) ∨ (False ∧ (False → p5)))) ∧ (p4 ∨ p3))) ∧ p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607042720566261473808761468028 : (((((((p2 ∨ (False ∧ (False → ((p2 ∨ p5) ∨ (p1 ∨ True))))) ∧ p5) → (((p3 ∧ (True → (True ∧ p3))) → p1) ∨ p1)) ∧ p3) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254651891766274517804962715928 : ((p3 ∧ p2) → ((((((p1 ∨ (False → (p4 → (p4 ∧ False)))) → (p4 → p4)) → (p4 ∧ True)) ∨ p3) ∧ p5) ∨ (p4 → (p5 ∨ (p1 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233895845633418906732049110772 : ((p4 ∨ (p4 ∨ False)) → (((p5 → True) → p1) ∨ ((p3 ∨ False) ∨ ((((p5 → ((p5 → (p1 → False)) → True)) → True) ∨ (p1 ∨ p5)) ∧ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148395492442895246426531723076 : (((p4 ∧ (p1 ∧ (((p5 ∨ p4) ∧ False) ∧ ((p1 → (p2 ∧ p3)) ∧ False)))) ∨ (p3 ∨ ((p2 → False) ∧ p4))) ∨ ((True → p5) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147115764965826460685310688754 : ((((p4 → p2) ∧ (((p1 → ((False ∨ p5) ∨ ((p5 ∧ (True → p3)) ∨ p5))) ∧ (p1 ∨ p2)) ∨ True)) ∧ p1) ∨ ((p4 ∨ False) → (True → p4))) := by
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
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174561598386327181680422663068 : ((((p2 ∧ p5) ∧ (True → p1)) ∧ ((False → p5) ∨ (p5 → ((p4 ∨ True) ∧ False)))) → (((p5 ∧ (False ∧ True)) ∧ (False ∨ (False ∨ p1))) ∨ p1)) := by
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
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34126642964653500615742998526 : ((True → (((p5 ∧ ((((True ∧ (True ∨ p4)) ∨ ((p3 ∨ False) ∨ p5)) ∨ (p2 ∧ p3)) ∧ p5)) → ((p3 ∧ p3) ∨ (p5 ∨ p4))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618562458999746590962697926792 : (((((p5 ∧ ((p3 → p2) ∨ p5)) → (p2 ∨ (((p4 → (p2 ∧ p3)) → ((p3 ∨ (p5 ∧ (p2 ∧ p4))) ∨ p1)) ∧ (p4 ∨ p1)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_691421108696089658313799786239 : (((((p3 → True) ∧ (p4 ∧ (p1 ∧ (((p1 ∧ True) ∨ (p2 ∧ p4)) → (p3 ∨ p2))))) → (((p5 → True) → False) → (p2 ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337665555839130724126982946839 : (p1 → (((((p4 ∧ (p5 ∧ p3)) ∧ False) → p4) → (((p4 → True) ∧ (p5 ∧ p5)) → (p5 ∧ p4))) ∨ (True → (((True ∧ True) → p1) ∧ p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53132524393644470316246886536 : ((((((p1 ∨ (p2 ∧ (True ∨ True))) ∨ p1) → (False ∨ p1)) ∧ p2) ∨ (False → ((p5 → p4) ∨ ((((p3 ∧ p5) → p3) → p1) ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218512481838378477923783485185 : (((p3 ∨ True) → (p3 ∧ False)) → (((p4 ∧ (p4 ∨ p3)) ∨ (p1 → (p1 ∨ (p4 ∧ ((False ∧ p4) → True))))) → ((p1 ∨ p2) ∧ (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h22 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h23 := h1 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h30 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h30
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- False on the left can always be used.
    apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h37 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h38 := h1 h37
      -- We need to get the right conjuct of h38 based on <expert-advice>.
      let h39 := h38.right
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h41 : (p3 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h42 := h1 h41
      -- We need to get the right conjuct of h42 based on <expert-advice>.
      let h43 := h42.right
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h45 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h46 := h1 h45
    -- We need to get the right conjuct of h46 based on <expert-advice>.
    let h47 := h46.right
    -- False on the left can always be used.
    apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261406910490199154114863931999 : ((p5 → p1) → ((p3 ∨ (p4 ∧ True)) → (p4 ∨ ((p2 ∧ (p4 ∧ ((p4 ∨ p4) ∨ (False ∧ (((p1 ∨ False) ∧ (p1 ∨ False)) ∧ True))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143063695539717948075337537196 : ((False → (((((p4 → ((p4 ∧ p2) ∧ p4)) ∧ p1) → True) ∧ p4) ∧ ((((p1 → (p5 → p5)) → p3) → p5) → p4))) → (p2 ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60839659403985086341058158082 : ((True ∧ (p1 ∨ ((((p3 ∨ (p3 → (p2 → False))) ∨ ((p1 ∨ (((p5 ∨ p1) ∨ p4) ∨ p5)) ∧ p3)) → p1) ∧ (p1 ∨ (p3 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744195037887396778763677453696 : ((((p1 ∧ p1) → ((True → p4) → ((((p3 → False) → (p2 ∧ p5)) ∨ (p1 ∧ True)) → ((p5 ∨ (p2 ∧ p4)) ∨ (True ∨ (p3 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188835241600764556747141326740 : (((((False ∨ p4) ∨ p3) ∨ False) ∨ ((True ∧ p5) ∨ True)) ∧ (((False ∧ (p1 ∨ (((p1 ∧ p4) ∧ p5) ∨ (False ∧ (p4 → p4))))) ∧ p5) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257123375911955389592744996927 : ((p2 ∨ p1) → ((((p4 → (p2 ∧ p2)) ∨ (((p3 ∧ ((True → (True ∨ p5)) → p1)) → (True ∧ False)) ∨ ((True ∨ p2) ∧ p2))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610966969661525493228766442518 : (((((((True ∧ (True → p4)) ∧ (False ∨ (p1 → p3))) ∧ ((p4 ∧ ((((True → (p5 ∧ False)) → p3) ∨ p2) ∧ p3)) ∨ p3)) → p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_658411492622275016138677661666 : ((((False ∨ (p2 ∨ ((p4 ∨ ((p1 → (p5 ∨ True)) → True)) ∧ ((p5 ∧ (p4 ∧ p5)) ∨ ((p1 ∧ False) ∧ (p4 ∨ p3)))))) ∨ (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681345529525960943151090038309 : ((((False ∨ (p4 ∨ ((((False ∧ ((p4 → ((False → p1) → True)) ∧ p4)) ∨ False) → (False ∧ False)) ∨ p3))) → ((p2 → (p4 ∨ p5)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159895060216826867695833232889 : ((((((p5 → p1) ∧ ((False ∧ p5) ∧ (((p2 ∧ p2) → p1) ∧ p4))) ∧ (False ∨ p4)) ∨ False) → True) → (p5 → ((p1 ∨ p2) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_63920362813149935427868031894 : ((False ∨ ((((((((p5 → (p2 → (True ∨ p5))) ∨ p2) ∨ p1) ∧ (p4 ∨ p1)) ∨ (p4 → ((p1 → p2) → False))) ∧ p1) ∧ p5) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134273203626475010031066672995 : ((((p1 ∨ p2) ∧ ((p1 ∧ (p4 ∨ True)) ∧ ((p2 ∧ (((True ∨ p2) ∧ ((False ∧ p1) → p2)) ∧ p2)) → True))) ∨ p1) ∨ (p5 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353568489053598411883116459911 : (p4 → (p3 ∨ ((p4 ∨ p1) → ((p3 → (True ∧ ((True ∧ p4) ∨ (p3 → p1)))) ∧ (p4 → (((True ∧ ((p3 ∨ False) → p2)) → p1) ∨ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179057794677935587080667815709 : (((p5 → p5) → ((((p3 ∧ p5) → p5) ∧ p4) → (False ∧ (p3 ∧ p5)))) ∨ ((((False ∧ (p5 → p2)) ∧ p5) → (False ∨ (p4 ∨ p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60241295163347556011539956392 : (((True → p5) → ((p3 ∧ ((False ∨ (p1 ∨ p1)) ∨ p2)) ∨ (p2 → ((p5 ∨ p1) ∨ ((p3 → (p5 ∨ (True ∨ (False → p3)))) ∧ p3))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184468276630672640334374030901 : ((((((p2 ∨ False) → p1) → (p5 ∨ p4)) ∧ p4) ∨ (p1 → False)) ∨ ((False → ((False ∨ p3) → p4)) ∨ ((((p1 ∨ p2) ∧ p5) → p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601745753189088845679321684131 : ((((p4 ∧ ((((((p3 ∨ p3) ∧ (p2 → p5)) ∨ p5) ∨ p3) → ((p1 ∨ True) ∨ ((p3 ∧ (p2 ∧ p1)) → (True ∧ True)))) ∨ True)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305806902014238727851615920968 : (p1 ∨ (((p2 ∨ (False ∨ p4)) → ((p3 → False) ∧ False)) → (p4 → ((p4 → p1) ∧ (p4 ∨ (((p3 ∧ ((True → False) → p3)) ∧ True) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (False ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178579614332507780815030498354 : (((p2 → ((p2 ∨ p3) ∧ (p1 ∨ p3))) ∧ (p3 ∨ ((p1 ∧ p1) ∧ p4))) ∨ (((True ∧ (p3 ∧ ((True ∧ p5) ∧ True))) ∧ p1) → (p2 ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328912734745123925529661116441 : (True → (((((False ∨ (p1 ∨ True)) ∧ p4) → True) → False) → ((((p3 ∧ p2) ∨ p5) ∧ ((p5 → p1) ∧ ((True ∧ False) ∨ (p3 → p1)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ (p1 ∨ True)) ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194103366416091805279252848960 : ((False → (((p1 ∧ (p4 ∨ (p1 → p1))) ∨ True) → p4)) → ((((p3 → ((False ∨ False) ∧ True)) ∨ (p2 ∧ False)) ∨ p1) → ((p3 → p5) ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116832388400476108020788990402 : (((p5 ∨ p4) ∨ ((((False → p1) ∨ (False ∨ (p5 ∨ p2))) → p1) → ((False ∨ (((p5 → p3) ∨ False) ∨ p1)) ∨ (p1 ∨ p2)))) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p1) ∨ (False ∨ (p5 ∨ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253645329326870648440710199457 : ((p1 ∧ True) → (False ∨ (((p4 ∨ (p2 → p4)) ∧ p4) ∨ (p2 ∨ (p5 ∨ (p2 ∨ ((((p5 ∨ ((False → p2) → p5)) → p4) ∨ True) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693969137798075975907144953397 : (((((((False ∧ False) ∧ p2) ∨ (((p5 → p4) → False) ∨ False)) ∨ (p2 ∨ True)) ∨ ((((True ∨ p3) ∨ (p2 → p1)) → True) ∨ (False ∧ p2))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_116502104343409869450776753354 : (((p3 ∧ p4) ∧ (p1 ∧ ((((((((p3 ∨ False) ∨ ((False ∨ p3) → p5)) ∧ p4) ∨ p3) → p5) → p4) ∨ (p1 → p5)) ∨ p4))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118677765488487147316417127282 : ((p4 ∨ (p5 → ((((p1 ∧ p5) ∨ p2) ∨ p3) → ((p5 ∨ p5) ∧ (((True ∨ p4) ∧ ((True ∧ p4) ∧ p2)) ∨ (p4 → p4)))))) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180412062068683000340413977883 : (((p5 → (((p1 ∧ (p5 → p5)) ∨ p5) ∧ (p3 → p5))) ∨ (p5 ∨ p5)) → (p1 ∨ (p3 → ((False ∨ p3) ∨ (p5 → ((p3 ∨ p3) ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40340449085541415833948701555 : ((((((p5 ∨ p5) ∨ (((p2 ∧ p4) ∧ ((p3 ∨ p5) → p2)) ∨ ((((p4 ∨ (p4 ∧ p5)) → p1) ∧ False) ∨ True))) ∨ p2) ∨ p1) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229843814286603334311475195796 : ((p5 → (p4 ∧ p3)) ∨ ((p1 → (((p5 → ((p3 → p4) ∨ p3)) ∧ p5) ∨ ((p3 ∨ False) ∨ ((p1 ∧ p1) ∧ True)))) → ((True → False) → False))) := by
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
theorem thm_5_vars_120058599723732790597314038603 : ((((p4 ∨ (p1 ∨ (p4 ∨ (p1 ∨ (p1 ∨ True))))) ∨ ((p4 ∨ p2) → (((p5 → p5) → (p3 → (p5 ∨ True))) ∧ p3))) ∧ p2) → (p5 ∨ p2)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350745830597122935321375424815 : (p4 → ((True → (((p4 ∨ p5) ∧ (((((False → p5) ∨ True) ∧ False) ∨ (False ∨ ((False ∧ p1) → p1))) ∨ (p3 ∧ (True → p2)))) ∧ p5)) → p5)) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343667986129052129603883597853 : (p2 → (True ∧ (p1 → (((p3 ∨ (False ∨ (p4 ∨ p4))) ∧ (((((p4 ∧ p1) ∨ (True ∨ p5)) ∨ True) ∧ ((True → True) ∧ p3)) ∨ p2)) ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54480996608912967828337227828 : (((((p5 ∨ p4) → (p4 ∧ p3)) ∨ (p1 ∧ p4)) ∨ ((True ∧ (((p4 → (p3 ∨ True)) ∨ (((p5 ∨ p1) → p5) ∨ p4)) ∨ p3)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48434164282665037292333501598 : (((p4 → (((((p3 → (p1 ∧ (p1 → True))) ∧ (p5 ∨ (p1 ∧ True))) ∧ p3) ∧ (p1 → (p3 ∨ p1))) ∧ (True ∨ True))) → (p5 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326882748025196552595644801934 : (True → ((((p2 → (False ∨ p1)) ∧ ((True → (p2 → ((((False → p4) → p1) ∨ (p4 → p5)) ∨ p3))) ∨ ((True ∨ p2) ∨ p2))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356299245874900153190834296278 : (p5 → (((p2 ∨ p5) ∨ ((True ∧ ((p2 → True) ∨ p1)) ∧ (((p1 ∨ False) ∨ True) → False))) → (((p3 → (p2 → p1)) ∨ (True ∨ False)) ∨ p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49121217462346128940283888467 : ((((False → ((p1 ∨ True) → (False → ((p1 ∨ (p3 ∧ p4)) ∧ (p3 ∧ p4))))) → ((p5 → False) ∧ (p2 → p3))) ∨ (p3 → (True ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178396523117762735449860885765 : (((((p5 ∧ p5) ∧ p2) ∧ ((p2 → p4) ∨ (p5 → p1))) → (False ∨ False)) ∨ (False → (p3 ∨ (True ∧ (((p2 ∨ False) ∨ (p2 ∨ p3)) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53352907579724146011513260407 : ((((((p3 ∨ ((p2 → p2) ∧ (p4 ∧ p1))) → p1) ∨ p4) ∨ p3) → ((p1 ∨ ((p1 → p4) → (p1 ∨ (p3 ∨ (p1 ∨ True))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350792688203514753036048936306 : (p4 → ((((p1 → False) → (((p2 ∧ (((p5 ∨ p1) → (False ∧ (p5 → False))) → p5)) ∨ (p5 ∨ True)) ∧ (p3 → p4))) ∧ p4) ∧ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185678033204151915039489085226 : ((p1 → ((p3 ∧ ((p2 ∧ (False ∧ p2)) → p2)) → (p4 ∨ p4))) ∨ ((p1 → (False → ((((p5 → False) ∨ False) → p1) → (p3 ∧ p5)))) ∨ p2)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57041247660217749588719183446 : (((p2 → (p5 → p4)) ∧ (p3 ∧ ((p5 ∧ p5) → (((False ∨ p1) ∨ ((p1 ∨ (p5 → (p3 → (p5 → p4)))) ∧ (p2 ∨ p3))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171549385042420963880160255014 : ((((((p2 → (p4 → (p2 ∨ (p5 ∧ True)))) ∧ (p5 ∧ p3)) → p2) → p2) ∨ p2) ∨ ((True → (p1 ∨ ((False ∨ (p2 ∨ False)) → True))) ∨ p1)) := by
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
theorem thm_5_vars_345611422284718647497138563923 : (p3 → (((True ∨ p1) → ((((p3 ∧ (p1 ∧ (p3 ∨ p2))) ∨ p2) ∨ (p1 ∧ (True → (False ∨ (p2 ∨ ((p3 → True) → True)))))) ∨ True)) ∨ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740319419266080603447798038368 : ((((p1 ∨ p1) ∨ (((p3 → p5) ∨ (((p4 → (((False ∧ False) → (p4 → True)) → ((True ∧ p3) → p3))) ∨ p5) ∨ (p4 ∧ False))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204326977460964607911874065092 : (((p3 ∧ (True ∨ (p1 → p5))) ∧ p1) ∨ ((p5 ∨ p4) ∨ (((((p4 ∧ p4) → p2) ∧ (p2 → p1)) ∨ p3) ∨ (((False → p3) ∨ p4) ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972093405466591746540183546404 : ((((True ∨ p1) → (((True ∨ p2) → ((p4 ∧ (p5 ∨ (p5 ∨ True))) → p2)) ∧ (((p4 ∧ (((False → p4) ∧ p3) ∧ p1)) → p5) ∧ False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53818654752860012286023400226 : (((((p4 ∧ (p5 ∧ (p3 ∧ False))) ∧ p2) ∨ (p1 → p4)) ∨ ((((p1 → p2) ∧ (p2 ∧ p1)) → (p1 → (p4 ∨ p4))) ∨ (p4 → True))) ∨ p4) := by
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
theorem thm_5_vars_329360906967812818993845882666 : (True → ((p2 ∧ (p4 → p5)) → (((False ∨ (p1 ∧ (((p5 ∧ (p5 ∧ (p2 → (p4 ∨ (p2 ∨ True))))) ∨ True) ∧ (p1 → p1)))) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590723817959077319269466842513 : (((((True ∨ ((((True ∨ p2) ∧ (p2 → (p4 → False))) → (True → p2)) → ((p4 ∧ ((p3 → (True ∨ False)) → False)) → p3))) → p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218428993801813881809326416356 : (((p2 ∧ p2) → (p2 ∧ p3)) → ((False ∨ (True ∧ p5)) ∨ (((p4 → True) → p5) → ((p2 ∨ (p5 ∨ p1)) ∨ ((p3 → p1) → (True → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709621323887248085906301350880 : ((((p2 ∨ (p1 ∧ ((p5 ∨ p2) ∨ (False → p4)))) → (p5 → ((((p2 ∧ (p5 → p4)) → ((p1 ∧ p5) ∧ p2)) ∨ p4) → (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210406862135330618580049831319 : (((p2 ∨ (p4 ∨ False)) ∨ True) ∧ (p2 ∨ ((p5 ∨ (False ∧ (True ∨ True))) → ((False ∨ ((((True ∧ p1) ∧ p1) → (p1 ∧ p2)) ∨ True)) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669910475867431243560764820780 : ((((((False ∧ ((p1 ∨ ((p1 → p3) ∨ False)) ∧ p4)) ∧ p1) ∧ (p5 ∨ (p1 → ((p1 ∨ p5) ∨ (p2 ∧ p3))))) ∨ (True ∨ (p4 ∨ p1))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_338228839614195273505532068093 : (p1 → (((p5 ∨ (p3 ∨ (p4 ∨ p4))) ∨ False) ∨ ((p1 ∨ ((p1 ∨ ((p4 → p3) ∨ True)) → ((p4 ∨ p5) → (p2 ∧ p3)))) → (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



