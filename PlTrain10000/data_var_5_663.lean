variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41345592759045048248602475851 : (((((True ∧ p4) ∨ (p3 ∨ (p2 ∨ (False ∨ (((True → p1) ∧ p2) ∨ (p1 ∧ p1)))))) ∨ (((True → True) ∨ (p2 ∨ p3)) → True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727773792811307646061856649871 : ((((False ∨ (True → False)) ∨ (((p4 ∨ p2) ∨ (p3 ∧ (p1 ∧ (p5 → ((False → ((p2 ∧ p4) ∨ p2)) → p1))))) ∨ ((p2 → p5) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319380385210521794150785372654 : (p4 ∨ ((False ∨ ((p5 ∧ (True → (p4 ∧ (((False ∨ p2) → p1) ∧ False)))) → p2)) ∨ (((False → p4) ∨ p3) ∨ ((False ∨ (False ∧ True)) ∨ p4)))) := by
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
theorem thm_5_vars_47747204918473119466136136827 : (((((p1 → (p2 → (False ∧ p1))) ∧ (((p2 ∧ (p2 → p3)) → p1) → ((((False ∧ True) ∨ False) → False) ∨ True))) ∨ p2) → (p3 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149805652222754869570224244135 : ((False ∨ (p3 ∨ (((True ∧ (((True ∧ (p3 ∨ False)) ∧ ((p3 → p3) → p2)) ∨ p4)) → (p4 ∨ False)) ∨ p5))) ∨ ((p1 → True) ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344781938281414166743173755200 : (p2 → (p4 → (((((p2 ∨ p2) → (((False ∨ ((False → False) ∧ p1)) ∧ (p5 ∧ (p5 ∨ True))) ∨ p2)) ∨ (False → False)) ∧ True) ∧ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807364444148655902486804083376 : (((p4 → (((True ∨ True) → (((p1 → False) → (p2 ∧ True)) ∨ p3)) ∧ (((True ∨ ((p1 ∧ (p3 → (False ∨ True))) ∧ p1)) → True) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14816687167477932810559410064 : (((((p1 ∨ (((True ∨ p1) ∧ (p5 ∧ (True ∨ True))) → (p5 ∨ p2))) → p3) → ((p5 → False) ∨ (p3 ∧ (p3 ∨ p5)))) ∨ (p5 ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (((True ∨ p1) ∧ (p5 ∧ (True ∨ True))) → (p5 ∨ p2))) := by
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
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h5.left
      let h13 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (p1 ∨ (((True ∨ p1) ∧ (p5 ∧ (True ∨ True))) → (p5 ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h20.left
      let h28 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h31 := h1 h17
  -- One of the premise coincides with the conclusion.
  exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780465851855636894050213209729 : (((p2 ∨ ((((((p2 → False) → p1) → (((p1 → p1) ∨ False) → p4)) ∧ p1) → p3) ∨ (p4 ∧ ((p1 ∧ p3) ∧ (False → (p1 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655767809763660824541384348345 : (((((((p1 ∧ (p2 ∧ ((p2 → p1) → True))) ∧ p2) ∧ (p4 → (((True → p2) ∧ p4) ∨ True))) ∨ (p2 ∧ (p4 ∨ p4))) ∨ (p3 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_258767670543133836416840474289 : ((True → False) → ((p3 → ((p5 → (False ∧ p3)) ∧ ((((False ∨ False) → p1) → (p5 ∧ (p4 → False))) ∧ ((p1 → False) ∨ (True ∨ p5))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206161026828037513762906779562 : ((p5 ∧ (((p4 ∨ p5) ∧ False) → p5)) ∨ (((p1 ∧ (False ∧ p4)) ∨ (p2 ∨ (p3 ∨ True))) → (p1 → (((p5 ∨ p3) → p2) ∨ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219387525019839480632584015919 : ((p3 ∨ (p1 ∧ (p5 → p1))) → (((True ∧ (p2 ∧ (p2 ∨ ((False ∨ p3) ∧ True)))) ∧ (p3 → p2)) ∨ (p4 → (p4 ∧ (p4 → (p2 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355625852607048063965143494630 : (p5 → ((p1 ∨ ((False ∨ ((((p5 ∨ p5) ∨ p4) → (((p3 ∧ p2) ∨ p2) ∧ p5)) ∧ p5)) ∨ (p2 → ((p2 ∨ p1) ∨ p5)))) ∨ (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198655295541223451361754215186 : ((p3 ∨ (False ∨ ((True ∧ p4) ∨ (p1 → p5)))) ∨ (p1 ∨ (((p1 ∨ p4) ∧ (p3 ∧ (p4 → ((p4 ∨ ((p2 ∨ p1) ∨ p1)) ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213556159681852662301214526806 : ((((p5 ∧ p5) ∧ p4) ∨ p4) ∨ (((p3 ∨ p1) ∨ p3) → ((p5 → p3) ∨ (p3 → (((p3 ∨ (p4 ∧ (p5 → (True ∧ p2)))) → p3) → True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318939233104777850940789071560 : (p4 ∨ (((p2 ∧ ((p3 ∨ ((False ∨ p5) ∧ (p1 ∧ p3))) ∧ ((p3 ∨ False) → p4))) → (p2 ∧ (p2 → (p5 → True)))) → ((p2 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171296334004987137879369735867 : (((((p4 ∨ (p5 → (((True ∨ p4) → (p4 ∧ p5)) ∨ p4))) ∨ p4) ∧ False) ∧ p3) ∨ (((True ∨ False) ∨ True) ∨ (((p3 ∨ False) ∧ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312915816114136688791655759897 : (p3 ∨ ((True → (p3 ∨ ((True ∨ p2) ∧ ((p2 ∨ (((((p3 ∧ p2) ∨ p3) ∧ p4) ∨ (False → True)) ∨ (p1 ∨ (p5 → p3)))) ∨ False)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751459613500682702307080263091 : (((True ∧ ((p2 → p2) → ((p3 ∧ (p1 → (((False ∨ False) ∧ (p2 → p3)) ∨ (p2 ∨ ((True → (p1 ∨ p1)) ∨ True))))) ∨ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41697133744706648744792813536 : ((((((p3 ∧ p1) ∧ (p5 ∧ p2)) → p5) → ((((False ∨ ((False ∨ p3) ∧ p3)) ∨ (((p2 → p5) ∧ p3) → p5)) → True) ∧ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41301190844744458940860207420 : ((((True → ((((p1 → p5) ∧ p3) ∨ (p2 ∨ False)) ∨ (False → (p1 ∧ ((p4 ∨ p2) → False))))) → ((False → p1) → (p5 ∨ True))) ∨ p2) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115266435751710695472399196794 : (((False ∧ (((True ∨ ((p1 ∨ p2) → True)) → p3) ∧ p5)) ∨ ((p3 ∧ ((p4 → (True ∧ p1)) ∧ (False ∧ True))) ∧ (p2 → False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180275490371577148472125508662 : (((p2 → (((p2 ∨ p5) ∧ ((p5 → (p1 → p4)) ∧ p4)) → p2)) → True) → ((p4 ∧ ((p4 ∨ True) ∨ ((p4 → (p4 → p4)) ∨ False))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51292626598286351677618408118 : (((p5 ∧ ((p1 ∨ ((((p2 → (True → p4)) → True) ∧ True) → ((False ∧ p1) ∨ p5))) ∨ True)) ∨ ((p5 ∨ p5) → (p1 → (p2 ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67522108293874850103177156426 : ((p1 → (((p4 ∨ p4) ∨ (p4 → (p3 → True))) → (((((p1 ∧ False) ∧ p5) ∨ ((False ∨ p3) ∧ p5)) ∧ p2) ∨ ((p2 ∨ p2) → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145121528122190779556954420411 : ((((False ∨ p4) ∧ ((((p5 ∧ p1) ∧ p4) ∨ True) ∧ False)) ∨ (False → ((p3 → (p5 ∨ p4)) ∧ (False ∨ p1)))) ∧ (False → (p5 → (p3 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310658615101109630826623805289 : (p2 ∨ ((((p2 → p5) ∨ True) ∨ p2) → ((False ∧ (True ∨ p5)) ∨ ((p3 → True) → ((p3 ∧ True) ∨ (((p4 ∧ p5) → (p1 ∨ True)) ∨ True)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324984002220734492807686697390 : (p5 ∨ ((p2 → p5) ∨ (p5 → ((((p2 ∧ ((((True → p2) → (False ∧ ((p2 ∨ p4) ∨ p2))) → p3) ∧ (p4 ∨ p2))) ∧ p4) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341701132385783910533213061534 : (p2 → ((((((p5 ∨ p1) ∨ p1) → ((p4 ∨ p1) ∨ ((p5 ∧ (p1 → p3)) ∧ (False ∧ p5)))) ∧ p4) ∨ (True → (p2 ∨ p3))) ∨ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303936629696933658893933774246 : (p1 ∨ (((((False → p2) → False) ∧ (p1 ∧ p4)) ∧ ((True ∧ ((p1 ∨ ((p5 ∧ False) → p4)) → ((p2 ∧ (p4 ∧ p3)) ∧ p3))) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612795637014124536769444384548 : ((((((True → p5) ∧ (p3 ∨ ((((p3 → (((p3 → p3) ∨ (p3 ∨ (p5 ∧ True))) ∧ p2)) ∧ p4) ∨ p1) → p3))) ∨ (p4 → p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_161152982831441542096543903774 : (((True ∧ p5) ∨ (p2 ∨ ((True ∨ True) ∨ ((((True ∨ p4) → ((p5 ∧ p4) ∧ p2)) ∨ p4) ∧ True)))) → ((p3 ∧ p4) ∨ (True → (True ∧ True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46229837644499644548621731047 : ((((((p1 ∨ p2) ∧ ((True → (((((p4 → p3) ∨ (False ∧ p3)) → True) → p4) → False)) → p2)) ∨ p2) ∨ (False → p4)) ∧ (True ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355643376757185166912868841726 : (p5 → ((p5 → (((p4 ∧ False) ∨ (p5 → p4)) ∧ ((p5 → ((p1 → True) ∧ False)) → ((((False ∨ False) ∨ True) → False) ∨ p2)))) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306422849136551360609690196518 : (p1 ∨ ((p4 ∧ p4) ∨ (((p4 ∧ ((p5 ∧ p3) ∨ (((p5 ∧ p1) → True) → (p1 ∧ p5)))) → ((p2 ∧ p4) ∧ (p2 ∧ (False ∧ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167074850852927966119504498055 : ((((((p3 ∨ p3) ∨ (((p2 ∨ p3) ∧ (p1 ∨ False)) → p5)) ∨ (p5 ∨ p4)) → p4) ∨ p1) → (p2 → ((((p2 → p4) ∨ False) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345502215741207716010829581317 : (p3 → (((((p5 ∧ p5) ∨ (p1 → ((((p4 → False) ∧ (p3 → p1)) → p5) ∧ p4))) ∧ p5) → ((p5 ∧ ((p2 → p1) ∧ p1)) ∨ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186679027471846311343144058504 : (((p4 ∧ ((p3 ∧ p5) → (True ∧ p1))) ∧ ((p2 → True) ∧ True)) → (p2 → ((p3 ∧ ((p1 ∧ p2) ∧ False)) ∨ (((p3 ∨ True) ∨ p2) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313281325878301364360568668835 : (p3 ∨ ((p3 ∧ ((p3 → (((p5 ∧ (((False ∧ p4) ∨ p3) → False)) ∨ ((((p5 ∨ (p4 ∧ p4)) ∨ p4) ∨ p1) → p3)) → p1)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779508685976766065963178042577 : (((p2 ∨ (((p2 ∨ (p5 ∨ ((p2 ∨ p3) ∧ p1))) ∨ (p3 → (p3 ∨ (((p3 → (((p1 ∨ p1) → False) ∨ p1)) ∧ p5) ∨ p2)))) ∨ p4)) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304064901601787663573810262189 : (p1 ∨ ((p1 ∨ ((True → (p2 ∨ (p5 ∨ (p2 ∧ True)))) ∨ ((p3 ∧ (((False ∧ False) ∧ p2) ∨ ((p3 ∧ p5) ∨ (p5 ∨ p5)))) → p5))) ∨ p3)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315130000628602758823341916623 : (p3 ∨ ((False ∧ (((p1 ∨ p4) ∨ False) ∧ False)) ∨ (True ∨ ((p3 ∨ p2) → ((p3 → p4) ∧ (p5 → (False ∨ (((p2 ∨ True) → p3) ∧ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136255037294156022427387574420 : (((p2 → (p5 → (p2 → (p1 ∧ False)))) ∨ (((p2 → ((p4 ∧ p2) → (((p4 → p5) → False) → False))) → p5) ∧ p4)) ∨ ((True ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256467777432127016677006707048 : ((False ∨ p4) → (((((((p5 → (p2 ∨ p2)) → p2) → (True ∧ p2)) → (p1 ∧ (p1 ∨ p2))) ∧ (p3 → p1)) ∧ (p4 ∧ False)) ∨ (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703475004019585446603372845126 : ((((p5 ∨ ((True ∧ p1) ∨ ((p3 ∧ True) ∧ (True ∧ p1)))) ∨ ((p3 ∨ p1) ∨ (((p4 ∨ (True ∧ ((p4 → True) ∧ p5))) → p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355529437812188729157848003867 : (p5 → (((((((p2 ∨ p1) ∧ (p2 ∨ p2)) ∨ ((((p2 ∨ (p1 ∧ p1)) → p2) ∧ p5) → True)) ∨ p2) ∨ (p5 ∨ True)) ∧ False) ∨ (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385062406131785195110944287417 : (((((False ∨ (p2 → (p2 ∨ ((((p5 ∨ ((p3 → (p2 ∨ p4)) ∧ False)) ∨ (True → ((p1 ∨ False) → p2))) → False) → p3)))) → False) ∨ True) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57109223681077363994799720483 : ((((p1 ∨ p2) ∧ p1) ∨ ((p5 ∧ (p4 → (p2 → ((((p5 ∨ (p3 → p3)) ∧ False) ∨ p1) → False)))) ∨ (p4 → ((p2 → False) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50219833267599371126670324090 : (((((p3 ∨ p4) ∧ ((p4 → (((p3 ∨ (p4 → p2)) ∨ p3) → (True → p1))) ∨ (True ∨ True))) ∨ False) ∨ (False ∧ (p1 ∧ (p2 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257378852956131604186440403837 : ((p2 ∨ p5) → ((((False ∧ p1) ∨ ((p2 ∨ ((False ∨ (p5 ∧ (p4 ∨ (p1 → p1)))) ∧ p3)) ∨ True)) ∧ (p3 → (p4 ∧ True))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783378636619874923788618790262 : (((p3 ∨ ((((False ∧ p3) → p5) ∧ (p4 ∧ ((p5 ∨ (p4 ∧ (p3 → True))) ∧ (p5 ∧ p4)))) ∨ (p1 ∨ ((p1 ∧ True) → (p4 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200696345357721818763603569264 : ((p2 ∧ ((p3 ∨ (p5 → p4)) ∧ (p3 ∧ p2))) → ((True → p5) → (p3 → (((False ∨ p3) ∨ (p2 → p2)) → ((True → p5) ∧ (p3 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h12.left
        let h20 := h12.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h21
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h32 := h2 h31
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h27.left
      let h35 := h27.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h37 := h2 h36
      -- One of the premise coincides with the conclusion.
      exact h37
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h1.left
      let h42 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h44.left
        let h47 := h44.right
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h44.left
        let h50 := h44.right
        -- One of the premise coincides with the conclusion.
        exact h49
  case inr h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h1.left
    let h53 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h54 := h53.left
    let h55 := h53.right
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h55.left
      let h58 := h55.right
      -- One of the premise coincides with the conclusion.
      exact h57
    case inr h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h55.left
      let h61 := h55.right
      -- One of the premise coincides with the conclusion.
      exact h60
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42962073007230541276039824800 : (((p5 → (((p2 → ((p5 ∧ p4) ∧ (((p4 ∧ (True → False)) ∧ (p1 → p1)) → ((True → False) → (p5 ∨ False))))) ∧ p3) ∨ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191838848623152099593108810130 : ((p3 ∨ ((p4 ∨ (True → p4)) ∧ (p3 ∨ (p2 ∧ p4)))) ∨ (p1 → ((p2 ∨ p1) → ((((p4 ∨ p3) ∧ (False → (p5 ∧ p4))) ∨ False) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109852692216527989775583561978 : ((p5 ∨ (p2 ∨ ((((p5 ∨ p4) → (p4 → (p4 ∧ (p3 ∧ p5)))) → p4) ∨ (p3 ∨ (True ∨ ((True ∨ p3) ∨ (p2 → p3))))))) ∧ (False → p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692236544600009351376390667046 : ((((((False → p5) → (p2 → (((p2 ∧ p4) → p5) ∨ (p3 → p5)))) ∨ p2) ∧ (p1 ∨ (p4 ∧ (((False ∨ p3) ∨ True) → (True → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148080181932317729620674345583 : ((((((p1 → (True ∧ p3)) ∨ (p3 ∨ (((p3 ∧ p3) ∧ (p1 ∨ False)) ∨ p4))) → False) ∨ p5) → (p3 ∧ p2)) ∨ (((True → True) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209428871463217543571053111253 : ((p2 → ((True ∨ p3) ∧ (p3 → p5))) → (((False → p1) → ((p1 → (p2 → ((p4 → p1) ∨ p3))) ∧ False)) → ((p1 ∧ p2) ∧ (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h11
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246768910590464439645823222028 : ((p5 ∧ p5) ∨ (((p1 ∧ p5) → p1) ∧ (((((((p4 → p1) ∧ p1) → ((p3 ∧ p1) ∧ False)) → p1) ∧ p2) ∨ (True → (p2 ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350092503859266671816647938458 : (p4 → ((((False ∨ (((p4 ∨ p2) ∨ ((False ∨ p2) → p1)) ∧ (p2 ∧ ((p2 ∨ p5) ∨ (p2 → p5))))) ∧ False) ∨ (False ∨ (False → p5))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608486899694855586170818913357 : ((((((((p5 ∨ False) → (p2 → ((((True ∧ p3) ∨ False) → p1) ∧ p1))) ∨ (p4 ∨ (p2 → ((p4 ∧ p5) → p3)))) → p1) ∨ False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_317093650823686892369982302496 : (p3 ∨ (p5 → ((((p1 ∧ ((((p3 ∨ (p3 ∧ False)) ∨ p2) ∧ (p2 → True)) → (p1 → (((True → p4) ∧ p1) ∧ p1)))) ∧ p2) ∨ True) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350749170181994611871688891812 : (p4 → ((True → ((p3 ∨ False) ∧ (((((p4 ∨ (p3 ∧ (p1 → (True → True)))) → (p2 → p1)) ∧ ((p3 ∧ p5) ∨ False)) ∨ p3) ∧ False))) → p2)) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186291271612073516459533152946 : ((((((p3 ∧ False) → p3) ∨ ((False ∨ True) ∧ p4)) → p1) → p4) → ((True → (((((False → (p4 ∧ p1)) → p4) ∨ True) ∨ p2) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618572764952279208110905048064 : (((((False ∨ (p4 ∨ (False ∨ p4))) → ((((p4 ∧ ((p1 ∧ False) ∨ p2)) ∧ ((False → (p1 ∨ p1)) ∧ (p2 ∧ p4))) ∨ p3) → p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60403060554089086296577310609 : (((p4 → True) → ((((p5 ∨ (p5 → p3)) ∧ (True ∨ (p2 ∧ p1))) ∧ (((p4 → ((p4 ∧ False) ∧ p5)) → p3) → p3)) ∨ (p2 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177926371547047621349712885413 : ((((((p5 ∨ p1) ∧ True) ∨ p3) ∧ (p5 ∧ ((p4 ∨ p5) → False))) ∨ True) ∨ ((((False → (((p5 ∨ False) → p3) ∧ p2)) ∧ p3) ∧ p1) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307686188004220800768982255387 : (p1 ∨ (p2 → (((p2 ∧ p4) ∧ ((p4 ∧ (True ∧ (True ∨ ((p1 → (False ∧ True)) → p4)))) ∨ p1)) ∨ ((((True ∧ p2) → False) ∧ p3) → False)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225356602976046218023933936952 : (((p1 ∨ p4) ∧ p3) ∨ (((p2 ∨ (((p2 → p3) ∨ p1) ∧ p4)) ∧ ((p2 ∧ p1) ∨ (p1 → p2))) ∨ ((False → p3) ∨ (p3 ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_171504640911823674238499809664 : ((((((p4 ∧ (p1 ∧ (p3 ∧ ((True ∨ p4) ∧ True)))) ∧ p4) ∨ p4) ∧ True) ∨ p3) ∨ ((p5 ∨ ((True ∧ (p3 ∧ p1)) → p4)) → (p3 → p3))) := by
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
theorem thm_5_vars_45916185875777661394973530095 : (((p4 → ((True ∨ (p2 ∧ ((p5 → True) → p1))) ∨ (p5 ∧ ((p1 ∨ (p4 → p4)) ∧ (((True ∨ (True ∧ p5)) → p4) ∨ p2))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172965636370285659770683906801 : ((p4 ∧ (((p4 → (((p4 → p5) ∨ p3) → (p5 → p4))) → p1) → (False ∧ p5))) ∨ (True ∨ (((((True → p3) → p1) ∧ False) ∧ p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265635507604850123339723576998 : (True ∧ (p2 ∨ (((((False ∧ p5) ∧ p5) ∨ False) ∨ (((((p2 ∧ ((p1 ∨ ((p1 → p1) ∧ False)) ∧ p5)) ∨ p3) ∨ p5) → p3) ∨ p2)) ∨ True))) := by
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
theorem thm_5_vars_258965797835341595604316227199 : ((True → p3) → (((p1 ∧ p4) ∧ ((False ∧ (((p2 ∨ p5) ∧ ((p2 → p5) → p1)) ∧ p1)) ∨ p5)) ∨ (((p4 → True) ∧ (True → p5)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67587098007046517186708145873 : ((p1 → ((p2 → p5) → (((p4 → p5) ∧ (((((p5 → (p2 ∨ (p5 ∨ p4))) ∧ p5) ∨ (True ∨ False)) → p3) ∨ (False ∧ False))) ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137040573637203128840501066368 : (((True → p2) → (True ∧ ((((((p4 ∧ (p4 ∨ p3)) ∨ True) ∧ (p5 → p4)) ∨ p2) ∧ (p2 ∨ p2)) ∨ (False → p1)))) ∨ (p4 ∧ (p3 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303913372240086573731395694001 : (p1 ∨ (((p5 ∨ ((p5 ∨ (((p1 ∨ p5) ∨ p4) ∨ (p2 ∧ p4))) ∨ p5)) ∨ (p2 → ((p3 → (((p4 ∨ p2) ∧ False) ∨ p3)) → p2))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162423296951531238349674591403 : (((((p3 → (p1 ∨ p2)) ∧ (True ∨ p4)) ∧ ((p1 ∨ ((p4 → p1) → p3)) ∧ p4)) ∨ True) ∧ ((False ∧ p3) ∨ ((p4 ∧ (p3 ∧ p3)) → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806518106769867463511541631623 : (((p4 → ((((p4 → (False ∧ (((p3 ∧ (p1 ∧ (p2 ∧ p2))) → (p2 ∧ True)) → (p2 ∨ False)))) → False) ∨ (False → (p3 ∧ p1))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166561104008420391554020114140 : ((p5 ∨ (p4 ∧ ((p5 ∨ p3) ∨ (((p2 ∧ ((p4 → (False ∨ p2)) ∨ p4)) → p5) → p1)))) ∨ (((p3 ∨ (p1 ∧ p4)) → True) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356561584727487018667741005962 : (p5 → (((((True → p5) ∧ True) ∨ p1) ∨ ((False ∨ p2) → p4)) → ((((p2 ∧ (True ∧ ((True ∧ p4) → True))) ∨ False) ∨ True) ∧ (True ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111296328472771064817636153922 : (((True ∧ ((((False → (p3 ∧ True)) → (p5 → (p4 ∧ p2))) ∨ p3) ∨ (p5 ∧ ((True ∨ (p5 → (p5 ∧ p4))) ∨ True)))) ∧ p5) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639417953330863118209165384051 : (((((p4 ∨ ((p5 ∧ p2) → p3)) → ((p4 ∧ (p1 ∧ (True → (p2 ∨ ((False → (p1 ∨ ((p4 ∧ False) ∨ p5))) → True))))) ∧ p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139894653708619382398321246941 : ((((False → (((p3 ∨ (((p2 → p2) ∧ True) ∨ (p5 → p1))) ∨ False) ∧ ((p2 ∨ True) ∧ p2))) → False) ∧ (p1 ∨ p4)) → (p3 → (False ∧ False))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (False → (((p3 ∨ (((p2 → p2) ∧ True) ∨ (p5 → p1))) ∨ False) ∧ ((p2 ∨ True) ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (False → (((p3 ∨ (((p2 → p2) ∧ True) ∨ (p5 → p1))) ∨ False) ∧ ((p2 ∨ True) ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h10
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h16 : (False → (((p3 ∨ (((p2 → p2) ∧ True) ∨ (p5 → p1))) ∨ False) ∧ ((p2 ∨ True) ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h17
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h16
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h20 : (False → (((p3 ∨ (((p2 → p2) ∧ True) ∨ (p5 → p1))) ∨ False) ∧ ((p2 ∨ True) ∧ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h21
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h21
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h22 := h13 h20
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115639018268565936951404763038 : (((((p1 → p2) → (p4 → p5)) ∨ p1) ∨ ((True ∧ (((p1 ∨ p5) → p4) ∨ p2)) → (((False → (p4 ∨ True)) → False) → p3))) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (False → (p4 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False → (p4 ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308367266123628349749290534921 : (p2 ∨ (((((((((p2 → ((((((p5 ∨ p5) ∧ p4) ∧ p1) → p3) ∧ p3) → True)) ∨ p2) ∧ p4) ∨ True) ∧ True) → False) ∧ p5) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133758704454405182392845046080 : (((((p2 → (p4 → (True ∨ False))) ∧ p4) ∨ ((((p5 ∧ True) ∨ True) → ((p1 ∧ (p2 ∧ p5)) ∧ p2)) → False)) ∧ True) ∨ (True ∨ (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56948234082755856747363999605 : (((p1 ∨ (p3 ∨ p3)) ∧ ((p3 → ((p5 → ((p2 ∨ ((False ∧ p2) ∨ p3)) → ((((True ∨ p2) ∨ p2) ∧ p1) ∧ p4))) ∧ p1)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774844055136499750943286531380 : (((False ∨ ((p3 ∧ ((False ∧ True) ∨ p3)) ∧ (((True → p1) ∨ (p1 ∨ (True ∧ p5))) ∨ (False ∧ (((p3 ∨ p1) ∧ (p4 ∧ p4)) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624505765386645610784995536515 : ((((p4 ∨ ((((True ∧ (p1 ∨ True)) ∨ p4) ∧ (((p2 ∧ p3) ∧ p3) → (p5 ∨ ((False ∧ (p5 ∧ (p3 ∧ p2))) ∨ p3)))) ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157743583424592114267118826452 : ((((p3 ∨ (((((p3 → True) ∨ False) → True) ∧ p3) ∨ p4)) ∨ p3) ∧ (((p1 ∨ p3) ∨ False) ∧ p5)) ∨ (((p2 ∨ p4) ∧ (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166215954151136423327383257484 : ((p2 ∧ (((p4 ∨ (p2 ∨ (p3 → p4))) → (True ∧ ((p4 ∨ (True ∨ True)) ∧ p1))) ∨ True)) ∨ (p4 ∨ ((False ∧ ((True → p4) → p2)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180241826980270229303156674752 : (((p5 ∧ ((((True ∨ p2) → p3) ∨ (p4 ∨ (p3 ∧ p4))) ∧ p1)) → p4) → (p2 ∨ (((p3 ∧ (((p2 → p1) ∧ p2) → p1)) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342574050886256697201256137895 : (p2 → (((p1 → (((p5 ∧ p5) → p2) ∨ True)) → ((p5 ∨ True) ∧ p4)) ∨ (p5 ∨ ((p1 ∧ False) ∨ (p5 → ((True → (p2 ∨ p2)) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150247323020263553154522876656 : ((p3 → ((((p2 ∧ (((p5 → (p1 → True)) → p2) → (p2 ∨ (p2 ∨ True)))) ∨ False) → False) ∨ (False ∨ p3))) ∨ (p1 ∧ (p2 → (p2 ∧ False)))) := by
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
theorem thm_5_vars_692417893115864598927740054307 : (((((False → ((((p5 → p1) → False) → (p3 → p3)) → (True ∧ True))) → p1) ∧ ((((p1 ∧ (p4 ∧ p1)) → False) → False) ∨ (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315029348093855426381355225659 : (p3 ∨ ((p1 ∨ ((p2 ∨ (False → (p2 → True))) ∧ p5)) ∨ (p5 ∨ ((p1 ∧ (((False ∨ p5) ∨ (p5 ∨ p5)) → p3)) → (p4 → (p3 ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936526308575803341367056215536 : ((((((p4 → p2) ∨ (p1 → p5)) ∧ p4) ∧ ((p4 ∧ p4) → ((((p3 ∨ (p2 ∨ p4)) → False) ∨ ((True → p3) ∨ p4)) ∧ (False ∧ False)))) → False) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320529660198031837434199871257 : (p4 ∨ (True ∧ ((((p4 ∨ p4) ∧ True) ∨ (False ∨ False)) ∨ ((True → p4) → ((True ∨ (p3 ∧ (p1 → True))) → ((p4 ∨ (p5 ∨ p2)) ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- One of the premise coincides with the conclusion.
    exact h18



