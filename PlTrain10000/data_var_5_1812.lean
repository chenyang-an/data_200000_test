variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206864871113884315525400608290 : (((((p3 ∧ p3) → False) ∧ p3) ∧ p2) → (((((p3 ∨ (p5 ∨ p2)) → (((p1 ∨ True) ∧ (p5 ∨ False)) ∧ p2)) ∨ p1) ∨ p3) ∧ (p5 ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (p3 ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111569791089341765559379013410 : (((((False ∧ (p1 ∧ p4)) ∨ ((p4 ∧ ((p4 → p5) ∨ True)) → (((p1 ∧ (p4 → False)) ∧ (p1 → p3)) ∨ p2))) ∧ p3) ∨ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348230261825563623818564210455 : (p3 → ((p5 → p1) → ((((p1 ∧ (((False ∧ (True ∨ p1)) → ((p5 ∨ True) ∧ p5)) ∧ (False ∨ ((p4 → p1) ∨ p2)))) ∧ p2) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238344129707633773123414358990 : ((False ∨ True) ∧ (p3 ∨ (True → (((p3 ∨ (((p3 ∨ (p3 → p3)) → (False ∨ p4)) ∨ p2)) → (False ∧ True)) ∨ (((p4 → p4) ∨ True) ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325931327949363499969644201597 : (p5 ∨ (p5 ∨ (((p5 → ((p5 ∧ ((p3 ∨ ((False ∨ p4) ∧ p2)) ∨ p1)) ∨ p1)) ∨ ((p2 ∧ False) → (p5 ∧ p4))) ∨ (p3 ∧ (p5 → True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165155836433697383020036160346 : (((((p2 ∧ (p1 ∨ p4)) ∨ p3) ∧ ((True → p3) → (p1 ∧ (False → True)))) ∧ (True ∨ p2)) ∨ ((False ∨ (((True ∨ p3) ∧ p4) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114532243164395609777108931116 : (((p4 ∨ (False ∨ (p5 → ((((True → p4) ∧ (p3 ∧ (True → (p3 ∧ p4)))) ∧ p4) → p2)))) → (p1 ∨ ((True → p2) ∧ p4))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319479038470395622023927673357 : (p4 ∨ ((((False ∧ (True ∨ p1)) → (False → ((p1 ∨ p4) ∧ p4))) ∨ p5) → ((p2 ∨ (False ∧ (False ∨ False))) ∨ (((p4 ∨ False) ∨ p4) ∨ True)))) := by
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
theorem thm_5_vars_171640318014465852331095902279 : ((((p4 ∨ p3) ∨ (p2 → ((p3 → (p3 → False)) → ((p3 ∨ p5) ∨ False)))) ∨ p4) ∨ (p1 ∨ ((False → p3) ∨ ((p3 ∨ (p5 ∧ p2)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41602177175663531261025223594 : (((((p3 → (p4 → (p1 → (p1 ∧ p4)))) → False) ∨ ((p4 → (True ∧ ((p4 → p4) ∨ ((False ∨ (False ∨ True)) → p5)))) ∨ False)) ∨ p3) ∨ p1) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803763521135702063500861493441 : (((p3 → (((False ∨ p1) ∧ (((p5 ∧ ((((True → p1) ∧ True) → (p3 ∧ (p5 ∨ p3))) ∧ (False ∨ p5))) ∨ p5) ∧ p3)) ∧ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655233679761166423529472777049 : ((((((p5 ∨ (((((p4 ∨ p2) ∨ p3) ∨ True) ∨ False) ∧ ((p5 ∨ (p2 ∨ True)) → p3))) ∨ (p3 ∨ False)) ∧ (p4 → p4)) ∨ (True ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38342958632517367016205727402 : ((((((True → p1) ∧ p2) ∨ ((p1 ∧ (p3 → ((p5 ∧ (p5 ∧ p5)) ∧ p4))) → p5)) ∧ (p1 ∧ (p1 ∧ (p5 → (True ∧ p4))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135024073517657152572575466327 : (((p2 → (p3 → (p1 ∧ (((((p1 → p5) ∧ p4) ∨ ((True ∨ p1) ∧ p4)) ∧ p4) ∧ (p1 ∨ p4))))) ∧ (p5 → p2)) ∨ (p2 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260674319250870412846103048043 : ((p3 → p3) → ((p4 ∨ (True ∨ (p1 → p5))) ∧ ((((p4 ∧ p1) → p3) → (p3 ∧ p2)) → (((p3 → p1) → p4) → ((p2 → p2) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338508902176047874039483899669 : (p1 → (((p5 ∨ p5) ∧ p2) ∨ ((((p3 ∨ ((p1 → p1) ∨ p5)) ∧ ((True ∧ (p4 ∧ (True ∧ True))) → (False ∨ p3))) ∨ (p3 → True)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51969316501963594749242149532 : ((((p1 ∧ (p5 ∧ p3)) ∨ ((True ∧ (p5 ∧ ((p3 ∧ p5) ∨ p2))) ∨ (p2 → p2))) ∨ ((((p2 ∧ (p2 ∨ p2)) ∧ p3) ∨ p5) → False)) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184825785410422145341164105157 : ((((True ∨ (False ∧ p2)) → p2) → ((p3 ∨ False) ∨ (p1 ∧ False))) ∨ ((p3 → ((False ∧ True) → p3)) ∨ ((True → ((p1 ∨ p4) ∧ p2)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323932746616186354655816550172 : (p5 ∨ (((p4 ∧ (((False ∨ False) ∧ p4) → True)) ∨ (((p4 ∧ p3) ∧ (p3 ∨ p1)) ∧ p4)) → ((p2 ∨ (True → ((p4 ∧ True) → False))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h21 := h16 h20
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : (p4 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h31 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h33 := h16 h32
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : (p4 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h26
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h38 := h16 h37
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h39 : (p4 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h26
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h40 := h38 h39
        -- False on the left can always be used.
        apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227157148442556512037685868390 : (((p5 ∨ p2) → p4) ∨ (p3 ∨ (p5 ∨ ((((p2 ∧ p5) ∨ (p3 ∨ (((p3 ∨ False) → (True → (p3 ∧ (True ∨ p5)))) → p5))) ∨ p5) ∨ True)))) := by
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
theorem thm_5_vars_64316962019929388294885387643 : ((p1 ∨ (((p5 → ((True ∧ False) ∧ ((((p1 ∨ p1) ∧ (False ∧ (p3 ∨ ((p1 ∧ p1) ∨ False)))) ∨ p4) → (True → p4)))) → p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40357136428187100676564811996 : ((((((p3 ∧ ((((p5 ∧ p4) → (p4 → p5)) ∧ p4) ∨ (True ∧ (p5 ∧ (p4 → (p3 → p4)))))) ∨ (p2 ∧ p3)) → p4) ∨ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50634455728042093381609318591 : ((((((p5 ∧ p4) ∨ False) → (((p4 ∨ True) ∨ (p1 ∧ False)) ∧ False)) ∧ (((p5 ∨ p1) ∧ p2) ∨ p5)) → (p4 → (p2 ∨ (p2 ∨ p2)))) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((p5 ∧ p4) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785459231768683153294797926714 : (((p4 ∨ ((((False ∨ (p1 ∨ p4)) ∨ (False ∧ p3)) ∨ ((p5 ∧ (p2 ∨ p1)) → ((p5 ∨ ((p5 → p2) ∨ (p1 → p1))) ∨ True))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_184476883924192021289265333226 : (((((False → p5) → ((p1 ∧ p5) → p3)) ∨ p1) ∨ (p4 → p3)) ∨ ((((p4 ∧ p2) ∧ p3) → ((False ∨ False) ∨ p3)) ∨ (p3 ∨ (p4 ∨ p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113935434728657369228883340068 : ((((((p3 → p3) → True) → ((p2 → p1) ∨ p4)) ∨ (((p3 ∧ p3) ∨ True) ∨ ((p3 ∨ False) ∨ False))) ∧ ((True ∧ p1) ∧ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63132352109424293532102280392 : ((p5 ∧ (((p3 → ((p4 ∨ p4) ∧ p3)) ∨ (True ∧ ((p1 ∧ p2) ∨ ((p5 ∧ (p1 ∧ (p2 ∧ p3))) → ((p5 ∧ p2) ∨ False))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662623021116151999700498599002 : (((((((p4 ∨ False) ∧ p3) → p1) ∧ ((p3 → p4) ∨ (((((False ∨ p2) → (p4 → p2)) ∧ p3) ∧ (p4 ∧ False)) ∨ False))) → (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199221815015304231227598520087 : (((p4 ∨ ((p4 → (True → False)) ∧ p3)) ∧ p1) → (((p5 ∨ (((p5 ∨ p5) ∨ ((((p5 ∧ p3) ∧ p2) ∨ p3) → False)) ∨ p4)) ∨ True) ∨ p3)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168799857129781377393842643044 : ((p2 ∨ ((((True ∨ p1) ∨ (p5 → (p2 → (False ∨ ((True ∨ p4) → p5))))) ∨ p1) → p2)) → (((p1 ∨ (True → (p4 → p5))) ∨ p5) ∨ True)) := by
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
theorem thm_5_vars_200272678445070116602007598900 : (((p3 ∨ (False → p4)) → ((p1 ∨ p4) ∧ p2)) → ((((p4 ∧ True) → ((p5 ∨ p5) ∨ (True → p5))) → (((p3 ∨ True) → p3) → p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258172487534470403597700721493 : ((p4 ∨ p4) → ((p4 ∧ ((((p2 ∨ p5) ∨ ((p3 ∨ (False ∨ p1)) → (p4 ∧ p4))) ∧ ((p4 → p2) ∧ True)) ∨ p5)) ∨ ((True → p1) ∨ True))) := by
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
theorem thm_5_vars_39426590085510683960375465925 : (((p4 ∧ (p4 ∨ (((p1 ∨ ((p1 ∧ ((((p1 ∨ (p3 ∧ (p3 ∨ p4))) → False) ∨ False) → p1)) ∨ True)) ∧ (p3 → p1)) ∨ p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192212106659856538411611822839 : (((((p3 → p3) ∧ (p3 ∧ (p3 ∨ True))) → p3) ∧ p1) → (((False → (((p2 ∧ True) ∨ True) ∨ p1)) → (p5 ∧ False)) → ((True ∧ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → (((p2 ∧ True) ∨ True) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4218281254444888605882868472 : (p5 ∨ (((p4 → p1) ∨ (((p3 → (True → ((p3 → p4) ∨ p2))) → p5) → ((((p4 → p5) → False) ∨ p1) ∧ p2))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809381264626475024873024566609 : (((p5 → ((p3 → (False ∧ (p5 ∧ ((p2 → False) → (((p5 ∧ p5) ∧ p1) ∧ (p5 → ((p3 → ((p1 ∧ p5) ∧ p2)) ∨ False))))))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40980511142505170873991060252 : (((((p3 → p1) → ((False ∨ p4) ∨ (p3 → (((((p3 ∨ p1) ∨ (True → False)) → True) → p3) → (p5 → p2))))) ∨ (p2 → p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51720446679050368007809625248 : (((((p2 ∨ (p3 ∨ (True ∧ p1))) ∨ True) ∨ (p1 ∧ (((p4 ∨ True) ∨ False) ∨ p3))) ∧ ((((p1 ∨ p2) ∧ (p4 → True)) → p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165663856806760985906888781728 : (((False ∧ (p3 ∧ (p3 ∧ (p1 ∧ p3)))) ∨ ((((p2 → False) ∨ p4) ∧ (p3 ∨ True)) ∨ p2)) ∨ (p5 → ((p1 → True) ∨ (p5 ∧ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134458877965920082548474014214 : (((((((p2 ∨ p4) ∧ p2) → (p1 ∧ False)) ∨ ((p2 ∨ p2) ∧ (p2 ∧ ((p1 ∨ (p1 → True)) ∧ p1)))) ∧ p1) → p3) ∨ ((p1 → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50276960732559930643365338354 : (((((p2 → p3) ∧ ((p3 ∧ (((p2 → p4) ∨ p3) → (p2 ∧ (p2 ∨ False)))) ∨ p5)) ∨ (True ∨ p1)) ∨ ((False ∨ p5) ∨ (p2 ∨ p3))) ∨ p1) := by
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
theorem thm_5_vars_157715925796859005230487580283 : ((((((True ∨ False) → p3) → p3) ∨ (((p1 → p1) ∨ (p2 → True)) → p1)) → ((True ∨ p3) → p2)) ∨ (p2 ∨ (p5 ∨ (p3 → (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45069246183140996795956682894 : ((((p5 → p5) ∨ ((p1 → (p1 → False)) → (p3 ∨ ((((p4 ∧ p1) ∧ p3) ∧ p5) ∧ ((True ∧ ((p4 → p1) → p2)) ∧ p2))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165594926064018949374716368088 : ((((((p2 → p5) ∨ p3) → (False → False)) ∨ p5) → (False ∨ (((p1 ∧ p2) ∨ p3) → p5))) ∨ (((False → False) ∧ p5) → ((p2 ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_63227936845873101195336171015 : ((p5 ∧ (((((p5 → (False → (p4 ∨ p5))) → (p5 ∧ p3)) ∨ (p2 ∧ p1)) ∧ False) ∨ (p1 ∧ ((False ∧ (p3 ∨ p3)) ∧ (p1 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26972132955042021304363386595 : (((p4 ∨ p5) ∨ ((((p5 → (((p1 → (p1 → (p3 ∨ (p1 ∧ (p3 → p4))))) → p1) ∨ (p5 ∧ p1))) ∨ (p5 ∧ p4)) ∨ True) ∨ False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191132212265310745433967935312 : ((((p2 ∧ True) ∧ p3) ∨ (((p2 ∧ p2) ∧ True) → p5)) ∨ ((((True ∨ (p1 → p2)) ∧ (False → p1)) ∧ True) → (p5 → ((True → False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51084648114652030874789661019 : ((((((p2 ∨ (((p2 ∨ p3) → ((p5 → p4) ∧ True)) ∨ (p1 → True))) ∧ p2) ∧ p1) ∧ p5) ∨ (((True → p4) ∧ (p5 ∨ p2)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638194190682195508673896758517 : (((((((p4 ∧ True) ∧ False) → (False → (p1 → False))) → (p3 → (p4 ∨ (p2 → (((True → p3) ∨ True) ∨ (False ∨ (p3 ∨ p1))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949831970788723630490315253310 : (((((p5 → False) ∨ False) ∧ ((p2 → (((p3 → (((True ∧ (p1 → (True ∨ (True ∨ False)))) ∧ p5) ∨ p2)) → p2) → (True ∧ p1))) ∧ p5)) → False) ∧ True) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_815438539096725946264383850322 : (((((p3 ∨ (p1 → (((((p1 ∨ False) ∧ (p2 ∧ (p4 → (((True → False) ∨ False) ∨ p2)))) ∨ (True ∧ p1)) → p3) ∧ True))) ∨ False) ∧ p1) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (((p1 ∨ False) ∧ (p2 ∧ (p4 → (((True → False) ∨ False) ∨ p2)))) ∨ (True ∧ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711339408187723547962392267430 : ((((p1 ∨ (((True ∧ True) ∧ False) ∧ p1)) ∧ ((p2 → (((p1 ∧ p2) ∧ (((p3 ∧ (p1 ∨ (False → False))) → p5) ∨ p5)) → p1)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122877243837873049557024718205 : ((((p2 ∨ (p5 → p5)) ∨ ((p4 ∨ p2) → (((p5 → p3) → (p2 ∨ p3)) ∧ (p5 ∨ (p2 ∧ p2))))) ∧ ((p5 ∨ True) → p1)) → (p3 → p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166186129226303072019847517141 : ((p1 ∧ (((((p3 ∧ (p1 ∧ p3)) → (False ∧ p3)) → (p3 ∨ False)) → (p3 → False)) → p2)) ∨ ((False ∨ (p2 ∧ p1)) → (p5 ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199689811046986702513175678753 : ((((p3 → p4) → (p2 ∧ (p5 ∧ p5))) → p5) → ((((p3 → (True → p3)) ∧ False) ∨ (((p5 → p2) ∧ p4) → (p3 ∨ p1))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676365586508612469522486698300 : (((((True ∧ p2) ∨ (((((p5 → (p5 → p2)) ∨ (p3 ∨ p1)) ∧ (False → p2)) ∧ True) → (p4 ∨ p1))) ∧ ((True ∧ False) ∧ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218168819013876278604195593734 : (((True ∧ p4) ∨ (p4 → p2)) → (((p5 ∨ (True ∧ (p1 ∨ False))) → (p5 ∨ p4)) ∨ (p3 ∨ ((((p4 ∧ (p5 → True)) ∧ p1) → p1) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173160251391456746001348441446 : ((p3 ∨ (p3 ∨ (((False → (p4 ∨ (False ∧ ((True ∧ p5) ∨ p5)))) → True) ∧ p2))) ∨ (((p4 ∨ p5) ∨ (((p5 ∨ p1) → False) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_214479296300513339849741022370 : (((p1 ∧ True) ∧ (p4 ∨ p1)) ∨ (p2 ∨ (p3 → (p2 → (p2 → (True → (((p2 ∨ (p2 ∨ True)) ∨ False) → (p1 ∨ (p2 ∨ (p1 ∨ p5)))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322311256425287679063466026662 : (p5 ∨ (((True → (p1 → ((p5 ∨ p1) ∧ (((p5 ∨ (True ∨ p4)) ∨ (((p5 → p3) ∨ (True → p2)) ∧ p1)) ∧ (p1 ∨ False))))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139621991072432061263701462114 : ((((p1 ∨ (p1 → (((p5 ∨ (p4 ∧ p4)) → p5) ∨ p1))) ∨ ((False → ((p4 → False) ∧ p2)) ∧ (p3 → p3))) → p3) → (p3 ∨ (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (p1 → (((p5 ∨ (p4 ∧ p4)) → p5) ∨ p1))) ∨ ((False → ((p4 → False) ∧ p2)) ∧ (p3 → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127162825403438739483033445379 : ((p1 ∨ (((False ∨ p3) ∨ ((p4 → ((((True ∧ p3) ∨ ((p2 ∧ (p4 ∨ True)) → p5)) ∧ False) ∧ (p4 ∧ p4))) ∨ p1)) → True)) → (p5 ∨ True)) := by
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
theorem thm_5_vars_168588943909656162917316990344 : ((p2 ∧ (True ∧ (((p4 ∨ p3) → False) → (False → (((p5 ∨ False) ∧ (False → p2)) ∨ p5))))) → ((((p4 → (True ∧ p3)) ∧ p1) ∧ False) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248876906690821542617772550668 : ((p3 ∨ p5) ∨ (((p3 ∧ ((True ∨ p2) → (p1 ∧ (p4 ∨ True)))) ∧ (p5 → ((p1 ∨ (((p2 → p1) ∧ p3) → p1)) → p1))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191283248261073053485676119696 : (((p4 ∨ False) ∧ (p3 ∧ (p5 ∧ ((False → p2) ∧ p1)))) ∨ ((((p4 → False) ∧ (((False → p1) ∨ p3) → p5)) ∨ (p4 ∨ False)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61275624194411577912666263685 : ((False ∧ (p3 ∨ ((((p5 ∨ (p4 → (p1 ∨ False))) ∧ True) ∧ ((((p5 ∨ p4) → ((p2 → True) ∧ p3)) ∧ False) ∧ p1)) ∧ (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111799185655077856385244180017 : (((((True ∨ ((((p5 ∧ ((p2 ∨ (p3 ∧ p1)) ∨ p1)) ∨ p5) → True) ∧ (False → (p4 → True)))) ∧ p5) → (p4 ∧ p1)) ∨ True) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2078966897966530807543180988 : ((((((p5 ∨ (((p1 → p5) ∧ True) ∨ p4)) ∨ True) → (p3 ∧ p5)) ∧ True) ∨ (False → p3)) ∨ (((p4 → p1) → False) → (p3 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674399635643770069280636548005 : ((((p2 ∨ ((True ∧ (p1 → (True ∧ p4))) ∧ (((p3 → (True ∨ ((True ∧ p2) → p1))) ∨ p5) → (p3 → True)))) → ((p2 ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317833571561029443814505872373 : (p4 ∨ (((p4 ∨ (True → p3)) ∧ ((p2 ∨ p4) ∨ (p5 ∨ (((((p2 ∨ p3) ∧ p4) ∧ (((p2 → False) ∨ p3) → p5)) ∨ True) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157488150045082854204110633446 : ((((p2 ∧ ((p3 → (p1 ∨ (p1 → p1))) ∨ p2)) → (((p3 ∧ p2) → p5) → p1)) ∨ (p5 → p5)) ∨ (((True ∨ p4) ∧ (p1 ∧ False)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631664781851044295160038931965 : (((((((p4 ∨ ((p4 ∧ (((p4 → p2) ∧ False) → (p4 ∨ p5))) ∧ p3)) ∧ p5) ∨ ((True ∧ True) ∨ ((True ∨ p2) ∨ p4))) → p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118484712182333757450093892548 : ((p3 ∨ ((((p5 ∨ (((p5 ∨ True) → p4) ∨ (p3 ∧ (((p3 ∧ False) ∧ p2) ∧ p5)))) → p1) ∧ True) ∧ ((True ∨ p1) → p5))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673210201904805441280995964625 : (((((((p3 ∧ (((p1 ∨ p5) → p4) → p2)) → p5) ∨ p3) → ((p5 ∨ (True ∨ (True → (p1 ∨ p1)))) ∨ p5)) → ((p4 ∧ p4) → p4)) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137444622219337629464962689750 : ((p4 ∧ (((p4 ∧ (p2 → (p4 ∧ (p1 → False)))) ∧ p2) ∧ ((p3 ∨ ((p1 ∧ ((p1 → False) → p3)) ∧ p4)) → p2))) ∨ ((p5 ∧ p1) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340110875422542779961776645971 : (p1 → (p3 → (((p2 ∨ (p3 ∨ ((True ∧ ((False ∧ p3) ∨ p2)) → p3))) → p2) ∨ (p1 → ((p4 → p3) → (((False ∨ p2) → p3) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47515275746517782466757454241 : (((p2 ∨ (True → (p4 → (((False → (p3 ∨ (p4 ∨ (False → False)))) ∧ ((p2 ∨ p4) ∧ ((p1 ∨ False) ∧ p2))) → False)))) ∨ (True ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152169936554074992502824662543 : (((p5 → ((p1 → True) → ((p3 → p4) ∨ p4))) ∨ ((p5 ∨ (p4 ∨ ((p2 ∨ p4) ∨ (p5 ∧ False)))) ∨ False)) → ((p5 ∨ p4) → (p2 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Disjunctions on the left can always be decomposed.
              cases h11
              case inl h12 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h12
              case inr h13 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h14 =>
              -- Conjunctions on the left can always be decomposed.
              let h15 := h14.left
              let h16 := h14.right
              -- False on the left can always be used.
              apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Disjunctions on the left can always be decomposed.
              cases h26
              case inl h27 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h27
              case inr h28 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h29 =>
              -- Conjunctions on the left can always be decomposed.
              let h30 := h29.left
              let h31 := h29.right
              -- False on the left can always be used.
              apply False.elim h31
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134726055325997752021771379283 : (((((True ∨ True) → p5) → ((True ∨ p5) ∨ (((((p3 → False) ∧ p5) ∨ p3) ∨ (True ∧ p2)) ∨ (p3 → p4)))) → p2) ∨ ((p2 ∧ p3) → p3)) := by
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
theorem thm_5_vars_48631957690591004575243392218 : ((((((p3 → ((p3 → p4) ∨ p1)) ∧ False) ∨ (p1 → ((p5 ∨ (p4 ∨ p3)) ∧ p2))) ∨ ((p3 ∨ p3) ∨ False)) ∧ (p4 ∧ (p2 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706960496530869946006224928723 : (((((((p2 ∧ p4) → p5) → (p3 ∧ p3)) ∨ True) ∨ (p4 → ((True ∧ p4) ∨ (((p4 → (p2 ∨ (p5 ∨ True))) ∨ p4) ∧ (p2 ∨ True))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_138888954576261616857118974130 : (((True → (((False → (((((p5 → True) ∨ p5) → (False → (p2 ∨ (p4 ∧ p4)))) → p3) ∧ p5)) ∨ False) ∧ False)) ∧ True) → (p2 ∨ (p1 → p4))) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762747753107794493080994146075 : (((p3 ∧ (((p2 ∨ True) ∧ (p5 ∨ (((p3 ∧ p1) ∨ p3) ∨ True))) ∨ ((((p2 → False) ∨ ((p1 ∨ p3) ∧ p1)) → (p2 ∧ True)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193628266381638430976770719610 : ((True ∧ ((p2 ∨ p1) ∨ (p5 → (False → (True → p4))))) → (((p1 ∧ (True ∨ p5)) ∨ ((p4 → p1) ∨ True)) ∧ (True ∨ ((p5 ∧ p5) ∨ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64980912393545619237368694351 : ((p2 ∨ ((p1 ∨ ((p5 → p5) → False)) ∨ (((p5 ∧ (p2 ∧ (False → p5))) → ((True ∨ p1) ∨ False)) ∨ ((p4 → p4) ∧ (p3 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348835445852592087030062074413 : (p3 → (p1 ∨ (p5 ∨ ((p4 → (((p4 ∧ (((False → p2) ∨ (p4 ∨ True)) ∨ False)) ∨ True) → p1)) → (p2 ∨ ((p1 ∧ False) → (p2 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49340483573176168723697546075 : (((True → (p2 ∨ (((False ∨ (p2 ∧ p2)) → ((((p1 → (p3 ∧ False)) → (p5 ∨ p1)) ∧ p2) → p1)) → p4))) ∨ ((False → p1) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187158618978889920429958809735 : (((p3 → p2) ∨ (p2 ∧ ((p3 ∨ ((True ∨ p5) → p5)) ∧ p4))) → (((p3 ∨ p1) ∧ p3) ∨ ((p4 → (p4 ∧ (True ∧ p2))) → (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263090905993419959915458924239 : (True ∧ (((((((((p4 → False) ∧ p5) → (p5 → p3)) → p1) ∧ (p4 ∨ False)) ∨ ((p2 ∧ p1) ∧ p5)) → (p4 ∧ p5)) → p2) ∨ (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165270325259116053709505911914 : ((((((False ∨ True) ∨ (True → (((p5 ∨ p2) → False) → p4))) ∨ False) → p5) → (p4 ∨ p5)) ∨ ((p5 ∨ False) ∨ ((p1 ∨ p2) ∨ (p4 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ True) ∨ (True → (((p5 ∨ p2) → False) → p4))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52810616052512404241778166352 : ((((True → (p4 ∧ (True ∧ (True ∧ p4)))) ∨ (((p1 ∧ p4) → p2) ∨ p1)) → ((((p5 → p2) ∨ False) ∨ (False → (p3 ∧ p5))) ∨ p4)) ∨ p3) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113507972450957315934210613491 : ((((((((p3 ∨ True) → p2) → p3) ∨ (p5 ∨ ((p3 ∨ p2) ∨ True))) → False) → ((p1 ∨ (True → p1)) ∧ p1)) ∨ (True → True)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44469736626802952713149782447 : ((((((True → (False ∨ p5)) ∧ ((p3 ∧ (p5 → p1)) ∨ False)) → p2) → (p2 ∧ (p1 → ((False ∨ (p1 → (p4 ∨ p1))) ∧ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49340611455815272588921920197 : (((True → (p3 ∨ (p2 ∧ ((p4 ∧ p4) ∨ ((p1 ∨ (((False ∨ p1) ∨ True) ∨ (True ∧ (p2 → False)))) → p4))))) ∨ ((False → False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764707477928427285377600784442 : (((p4 ∧ ((False ∨ ((False ∧ (p2 ∨ ((p2 ∨ True) ∨ p2))) ∨ (p2 ∧ (((p5 → (False ∨ p5)) ∧ (p3 → (p5 ∧ p3))) ∨ p1)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151116819797536920204318041956 : ((((p5 ∨ ((p1 ∧ (((p5 ∨ p2) ∨ (p3 ∧ (False ∨ (p2 ∨ p5)))) → p4)) ∨ (p4 ∧ p2))) → p5) → p5) → (((p4 ∨ False) ∧ p2) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51978548238423155112448455701 : ((((p2 ∨ p1) ∧ ((p2 ∨ (((p4 ∨ True) ∨ (p1 → p4)) → p1)) ∨ (p2 ∨ p3))) ∨ (p5 ∧ ((p2 ∨ ((p2 → False) ∨ True)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214435540981330742857444573531 : (((p4 → (p1 ∧ p1)) → p4) ∨ ((p3 ∧ p1) ∨ ((p2 ∨ (p1 → ((p2 ∨ True) ∧ (((p2 ∧ p3) ∧ p4) ∨ p3)))) ∨ (True ∨ (p5 ∧ p2))))) := by
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
theorem thm_5_vars_705667139360542997619761559612 : ((((((True ∨ False) ∧ (p4 ∧ p1)) ∧ (p5 ∨ p4)) ∧ ((((False → p5) ∨ (False → ((p2 → p3) → p5))) ∨ (p3 ∧ (False ∨ p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140731472865053639842743967088 : (((((((False → (p5 ∨ True)) → p5) ∨ (True → (p5 ∧ p2))) ∨ True) ∨ p1) → (((p4 ∨ (p3 → p5)) ∧ p1) ∧ p2)) → (p2 ∧ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((False → (p5 ∨ True)) → p5) ∨ (True → (p5 ∧ p2))) ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



