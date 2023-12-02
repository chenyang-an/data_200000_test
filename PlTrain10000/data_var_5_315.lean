variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68153009866274194229413174381 : ((p3 → (((p2 → (True ∨ ((False ∧ (True → False)) ∧ False))) → (((p5 → p5) ∨ True) ∧ ((True → True) → ((p2 ∧ p1) ∧ False)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240042482963186339701102296688 : ((p4 ∨ True) ∧ (p1 ∨ ((False ∧ (((p1 → False) → (True ∧ ((((p2 → (p3 ∧ (p4 ∧ False))) → p5) ∨ p2) ∧ p1))) ∨ p5)) ∨ (True ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658249264562604931811021220066 : ((((p5 ∧ (p1 ∧ (p4 ∨ ((True → p4) ∧ ((p3 ∨ (((((True → False) ∧ p3) → p1) → p4) ∧ (p5 ∨ False))) → False))))) ∨ (p2 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_191517118645863113062649113382 : ((False ∧ ((p1 ∨ p3) ∧ ((False → p1) → (p4 ∧ p4)))) ∨ (True ∧ (False ∨ ((True ∨ ((((True ∧ (False → p4)) → True) ∨ p1) ∨ p2)) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60701121483510462100724699753 : ((True ∧ ((p3 ∨ (p1 ∧ (p3 ∧ (p2 ∧ (True ∨ (p4 → p1)))))) → ((p1 ∧ (((False → (True ∧ p3)) → p4) ∧ p3)) ∨ (p3 ∧ p3)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742384023110253969816538040293 : ((((p1 → p4) ∨ ((True ∨ p1) → (((True → (p2 → (p2 → p5))) → (((p4 → (p4 ∧ (p1 → p3))) ∨ (False → p5)) ∨ p1)) ∧ True))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111171487122716673883454960974 : ((((((p3 ∨ True) ∧ p2) ∨ p2) ∨ (False ∧ (p1 ∧ (False ∧ (((True ∨ (True ∨ (p5 ∨ (p2 ∨ p1)))) ∨ p2) ∧ p1))))) ∧ p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747124073583052934892065964560 : ((((p5 ∨ True) → (((((p1 → (((p3 → False) → p2) → (((False ∧ p3) → True) ∧ (p3 ∨ p4)))) → False) → p2) → (p3 ∨ False)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59277231102628167245960402574 : (((p3 ∨ p2) ∨ (((((((p4 ∨ p3) ∨ ((p3 ∧ (False ∧ ((p5 → p2) ∨ True))) ∧ p2)) ∨ True) ∧ True) ∨ (True ∧ p3)) ∨ False) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_323651436652742019586857081233 : (p5 ∨ ((((((((p3 ∨ p1) → (p3 → p2)) ∧ p1) → p1) → (((p5 → p4) → True) ∧ p5)) → p2) ∨ p5) ∨ ((p3 ∧ False) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_352876950663076522898780413706 : (p4 → (True ∧ ((p5 ∧ (((((p3 ∨ False) ∧ ((p4 ∨ (p1 ∧ True)) ∨ p2)) ∧ (p2 ∧ (p4 ∨ (p1 → p4)))) ∧ p2) ∧ True)) ∨ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39964951351540234629241850127 : (((p4 → (((True ∧ p5) ∨ (p4 ∧ (p3 ∧ p3))) → (((p1 ∨ (False ∨ ((True → (True ∨ False)) ∨ p4))) → p1) ∧ (False ∧ p4)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47906746646107389517134881923 : ((((((p5 ∧ ((p4 ∨ p4) ∨ p4)) ∨ (p1 → ((p4 ∧ True) → (p2 ∧ (True ∧ (True → p3)))))) → False) → (p5 → p3)) → (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775800083313116671075116832772 : (((False ∨ (p5 ∨ (((p5 → p1) ∧ (p3 ∧ ((((p5 → False) → (p3 ∧ True)) ∧ True) → (((p1 → False) ∨ (p1 → p2)) ∧ p5)))) → p5))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 → False) → (p3 ∧ True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780608728084419315457569187568 : (((p2 ∨ ((True → (((p1 ∧ (False ∨ p2)) → False) ∨ (p2 ∧ True))) ∨ (p3 ∨ (p4 ∨ ((((True ∨ p2) ∨ True) ∧ (p5 ∧ False)) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111725190818772896255285254867 : ((((((p5 ∨ p4) → p4) → (p1 ∧ (True ∧ ((p5 → (p4 ∨ True)) ∧ ((p3 ∧ p1) → (True ∧ (True → True))))))) → p2) ∨ True) ∨ (p3 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699433409206591274466125486626 : ((((((((p4 → False) ∨ (p3 ∧ (p1 ∨ p2))) → p4) ∨ p2) ∨ p4) → ((p2 ∨ ((False → (True ∨ (p3 ∧ p3))) → False)) → (False ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : (False → (True ∨ (p3 ∧ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h13 := h8 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h16 : (False → (True ∨ (p3 ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h16
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56207850726103722118087756614 : (((False ∨ (False ∨ (p1 ∨ p5))) ∨ (((p5 ∨ ((p4 ∧ (p1 → False)) → ((p5 ∨ p1) ∨ (p4 → p2)))) ∧ (False ∧ (False ∨ p4))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673311321448119718823142134822 : ((((((p4 ∨ p3) → ((True → (p3 ∧ True)) ∧ p3)) → ((p4 ∧ (p1 ∧ (p3 ∧ (p2 ∨ p3)))) ∧ (p2 → p3))) → (True ∧ (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312348916170502557578325223459 : (p2 ∨ (p3 → ((((p4 → (p2 ∧ p1)) → ((((p1 ∧ p5) ∨ p2) ∨ (p3 → p2)) ∨ (((True → False) ∧ False) ∧ (p2 ∧ False)))) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117095895855484282124238160555 : (((p1 → p3) → (p4 ∨ ((True → ((((p1 → ((p2 ∧ (p4 ∧ True)) → p3)) ∧ p3) ∨ (True ∧ (p5 → p3))) ∨ p3)) → False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712108805560358435145860799884 : (((((p3 ∨ ((p4 ∨ p1) ∨ p4)) ∨ p3) ∨ (p4 ∨ (True ∧ ((p5 → ((p4 ∧ p2) ∧ p5)) ∨ (((True ∧ p2) → (p2 ∨ p2)) ∨ p4))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265842391590942677229960938835 : (True ∧ (p5 ∨ ((((True → (p5 → p5)) → p5) ∧ p4) ∨ (((p4 ∧ False) ∨ p3) ∨ (False → ((((True ∧ True) ∧ (p1 ∨ False)) ∨ p4) ∧ p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246061468380982417190007795898 : ((p4 ∧ False) ∨ (p2 → (True ∧ ((((((p5 → (p5 ∨ p5)) ∧ (p3 → True)) ∧ (p5 ∨ p2)) → p5) ∨ ((False ∧ p4) ∨ p2)) ∨ (True ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662996625525202101760137724619 : ((((((p3 → p3) ∨ p5) → (p3 ∧ ((p1 ∨ ((p4 → (((p1 ∧ True) → p4) ∧ p4)) ∧ p3)) ∧ ((False → p1) ∨ p4)))) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_866771347480235793065020589101 : (((((p2 ∧ (p1 ∨ p4)) → (((p4 ∧ True) → False) → (((p1 → (False → p3)) ∧ p1) → ((False → True) ∧ ((False ∨ False) ∨ p1))))) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p1 ∨ p4)) → (((p4 ∧ True) → False) → (((p1 → (False → p3)) ∧ p1) → ((False → True) ∧ ((False ∨ False) ∨ p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254027806543728244190356316921 : ((p2 ∧ True) → (((p1 ∧ ((p4 ∧ p1) ∨ ((((p5 ∧ p4) ∨ p4) ∧ p2) ∧ (p5 ∧ p5)))) ∧ (False → (((p4 ∧ p5) ∧ p1) ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_808720383356311801515027370665 : (((p4 → (p2 → (p5 → (p2 → (((p1 ∨ ((p3 → ((p4 ∧ p3) ∨ False)) → ((p2 → p2) ∧ p2))) ∨ ((p4 ∨ True) ∧ p3)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117000388819472114545584866806 : (((False ∨ True) → (((p1 → (((p5 ∨ True) ∨ ((p4 → (p1 ∨ p2)) → ((p2 → p2) ∧ p2))) ∧ p1)) → (True ∨ p5)) → p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259143133276200286320890723953 : ((False → True) → (((p2 ∨ (False → p4)) → (((p2 ∨ p2) ∧ (False ∧ ((p5 ∧ p2) ∨ ((p5 ∧ p1) ∧ p2)))) ∨ True)) ∧ (p5 → (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225235310811691349097162138639 : (((p5 ∧ p4) ∧ True) ∨ ((((p4 → ((p3 ∨ ((p3 → p5) ∧ False)) → False)) → p2) → (p1 ∧ p5)) → ((p4 ∨ ((p1 ∧ p5) ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132678274712071561067817990713 : ((False ∨ ((((((p3 → p1) ∨ p4) ∨ (p3 → (p4 → (p2 → p1)))) → p1) ∨ True) ∨ (p4 ∨ ((p4 ∨ p4) ∧ p2)))) ∧ (True ∨ (p5 ∧ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200952315612155185879713990161 : ((p2 ∨ ((((p2 → p2) ∨ p3) ∧ p3) → p4)) → ((p2 → (p5 ∧ p1)) ∨ ((True → (True ∧ ((((p2 → p5) ∧ False) → True) ∨ p3))) → True))) := by
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
theorem thm_5_vars_903182692386459771753898406577 : ((((p4 ∧ (((p4 → (((False → p4) → (p3 ∨ (p2 ∨ p4))) ∧ p4)) ∨ ((False → p1) → p2)) → False)) ∧ (True ∨ (p1 → (p4 → p3)))) → p2) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p4 → (((False → p4) → (p3 ∨ (p2 ∨ p4))) ∧ p4)) ∨ ((False → p1) → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : ((p4 → (((False → p4) → (p3 ∨ (p2 ∨ p4))) ∧ p4)) ∨ ((False → p1) → p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h12
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191502752046753743035639938417 : ((False ∧ (((p1 → (True ∨ (p4 ∨ p2))) ∧ p4) ∨ True)) ∨ (((p4 ∧ ((p2 ∧ p3) ∨ p4)) ∨ p4) → (p2 ∨ ((p2 ∧ (p4 ∨ p4)) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234020127994875928084975573232 : ((p5 ∨ (p5 ∨ p1)) → ((p4 → (p3 → (((((p4 → True) → ((p4 ∧ (p5 → False)) ∨ True)) ∨ True) ∧ (True ∨ p3)) ∧ p3))) ∨ (p2 ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185465549975862302614739031957 : ((p1 ∨ (((p2 → (p1 ∨ False)) ∧ (p5 ∧ p4)) ∧ (True ∨ p2))) ∨ ((((p1 → (True ∨ (False ∨ (False ∨ True)))) ∨ p1) ∨ (p3 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142095683437418116050010688343 : ((True ∧ (False ∨ (p1 ∧ ((True → (p2 ∧ (((((p5 ∨ p4) ∧ (True ∧ p1)) ∨ p4) ∨ True) → (p3 ∧ p4)))) → p1)))) → (p2 → (p3 ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995960156902586816113179996241 : (((p5 ∧ (p1 ∧ ((True ∨ (p2 ∧ p5)) → ((((False ∨ (((p4 ∨ (p5 ∨ p5)) ∧ p5) ∨ p3)) → p3) ∧ ((p2 ∨ p1) ∨ False)) ∨ p3)))) → p3) ∧ True) := by
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
  have h6 : (True ∨ (p2 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h13 : (False ∨ (((p4 ∨ (p5 ∨ p5)) ∧ p5) ∨ p3)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h14 := h9 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h16 : (False ∨ (((p4 ∨ (p5 ∨ p5)) ∧ p5) ∨ p3)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h17 := h9 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39580590256683233922839922275 : (((p1 ∨ (p4 ∧ ((p3 → ((p5 ∧ (p2 → p1)) ∨ p2)) → (p1 ∨ ((True ∧ p3) ∨ (p3 → (True → ((p5 ∧ False) ∨ p4)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218060885116487042005924528649 : (((p4 ∨ True) ∧ (True ∨ p5)) → (((((False ∧ ((p3 → p4) → True)) ∨ (((False ∨ (p1 ∨ p1)) ∨ True) ∧ p3)) ∨ p4) ∨ True) ∨ (False → p3))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61854735992971445493198018503 : ((p2 ∧ (((p4 ∧ ((p3 → (p1 → p3)) ∧ (p2 ∧ False))) ∨ (p1 → (p3 ∧ ((((p3 ∨ False) → False) → p4) ∧ (p2 ∧ True))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168181100914047976630836525898 : (((True → (False ∧ p2)) ∧ (p4 ∨ (p5 → ((((p3 ∨ p4) ∨ p3) ∧ True) ∨ (True → False))))) → (((False ∨ p4) → (p1 → (p1 → p3))) → p3)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134308518636798049243623714225 : (((True ∧ (((p2 ∧ (p2 ∨ p5)) → p3) → (p5 ∧ (((p2 ∨ ((p1 ∧ (p3 ∨ p2)) ∨ False)) → p5) → p5)))) ∨ p5) ∨ ((p2 ∧ False) → False)) := by
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
theorem thm_5_vars_336118008127209405359441494111 : (p1 → (((((((True ∧ p1) → (p4 → p3)) → (((((True ∧ p4) ∨ p3) ∨ p2) ∨ p2) → (p5 ∨ p3))) ∧ True) → (p4 ∨ False)) ∨ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354016739664830839218453537214 : (p4 → (p4 → (((((((p5 ∧ p5) ∧ ((False → p2) ∨ True)) ∨ (((p2 ∨ p5) ∧ False) ∨ ((p1 ∨ True) ∨ True))) ∧ True) ∧ p1) ∧ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64571324166199110881943484536 : ((p1 ∨ ((p4 ∧ (False ∧ p1)) ∨ (((((p5 → p4) ∨ p1) → (True → (p3 ∨ p1))) ∨ (True ∨ (p5 ∨ p4))) ∧ ((p2 → p2) ∨ p2)))) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50459670732777772701534588744 : (((p4 ∨ (p5 ∨ ((((p1 ∨ (p3 ∧ p4)) ∨ (((p2 ∧ (p2 ∨ True)) → p4) ∨ p3)) ∨ True) ∧ True))) ∨ ((p2 → (p4 → True)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588166475855374296007866181499 : ((((((p2 ∧ (((p2 ∨ (False ∨ p2)) → p5) → (p3 ∨ True))) ∧ ((((((False ∨ p3) → False) ∧ p5) ∨ p3) ∨ p2) ∨ p3)) ∨ p3) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42206290276847249785833347490 : (((True ∧ (p5 ∨ (((p2 → False) ∨ (False → True)) ∧ ((p2 ∧ ((p3 ∨ True) → (p2 ∧ (p4 ∨ p5)))) ∨ ((False → p4) ∨ p4))))) ∨ p4) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86013192408181214085803513547 : (((((p2 → False) → True) → (False ∨ ((False → p5) ∧ False))) ∧ (((p1 → (True ∨ p1)) → (False → True)) ∨ ((False ∨ p1) ∨ (p1 ∨ p3)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 → False) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : ((p2 → False) → True) := by
          -- Implications on the right can always be decomposed.
          intro h17
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h18 := h2 h16
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : ((p2 → False) → True) := by
          -- Implications on the right can always be decomposed.
          intro h26
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h25
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307851900059855468570707765785 : (p1 ∨ (p5 → ((p3 ∨ (((p1 ∧ True) ∨ (((p2 ∨ p3) ∧ p2) → ((True ∨ (True → p2)) ∧ p1))) ∨ ((p3 ∨ p3) ∨ (True ∨ p1)))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159802019620917892388050442051 : (((p3 ∧ (((True ∧ ((p1 ∨ (p3 ∧ True)) ∨ p2)) → (p2 ∧ p3)) ∧ ((False ∧ p3) → True))) ∨ p2) → (((p4 ∧ (p5 → p1)) ∨ p2) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True ∧ ((p1 ∨ (p3 ∧ True)) ∨ p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40602366502223816851757283908 : (((((((False → (p2 ∨ p1)) ∨ ((((p2 ∨ False) → p4) ∨ (False ∧ ((p2 ∧ False) → (True ∨ p1)))) → p2)) ∨ True) ∨ p1) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42036614444793720653881682879 : ((((p4 ∧ p2) ∨ ((p3 ∧ (((p1 ∧ (True ∨ ((((p1 → p3) → p4) → True) ∨ p5))) ∧ False) ∨ ((p5 ∨ p1) → p5))) → p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60284036539120696261608660048 : (((p1 → True) → (((p2 ∨ (p3 ∨ p5)) → (True → ((True → ((p1 → True) → ((True ∨ (True → p2)) → p1))) ∧ (p3 ∧ p1)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135794604373759202695672747691 : ((((p3 ∨ p4) ∧ ((p5 ∨ p5) → (p5 ∧ (((p1 ∧ True) → False) ∧ True)))) → (p1 ∧ (p5 → ((p4 ∧ p2) → True)))) ∨ (False → (p4 ∧ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38234693921735138178810588066 : ((((p5 → (p1 ∨ (p1 ∧ ((((p4 ∧ (p1 ∨ p3)) ∧ p1) → p3) ∨ ((True → p3) → (p2 ∧ p4)))))) → (p4 ∧ (p2 → p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307632428526623376818489819496 : (p1 ∨ (p1 → ((p5 ∨ ((True → (p2 ∨ p1)) ∧ p4)) ∨ (p5 ∨ (((False → p5) ∧ (p1 ∧ (False → p5))) → (((p2 ∨ False) ∨ p5) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233727714177850095376636895602 : ((p3 ∨ (p2 ∧ p1)) → ((((p5 → p5) ∧ (((p4 → False) ∧ ((False ∨ False) ∨ p1)) → p2)) ∨ (False ∨ ((p3 ∧ False) ∧ p5))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710557579758603949729526416562 : ((((((p2 ∨ p2) ∨ False) ∧ (p2 ∧ p1)) ∧ ((False → ((True ∧ ((p1 ∧ (True → (p1 → (p1 ∧ True)))) ∨ p4)) → (p3 ∧ p3))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729996490141122987582559984028 : (((((True ∨ p2) → False) → (((p3 → p1) → ((True → p4) ∧ (False ∧ False))) ∨ ((((p2 ∧ p3) → ((p2 ∧ False) → p1)) ∨ True) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115615180339391663636144197829 : (((p5 ∨ ((p4 → False) → (p1 ∨ p3))) ∧ (((False ∨ (p2 ∧ ((p3 ∨ True) ∨ ((p1 ∧ p2) ∨ p2)))) ∨ p2) ∧ (p5 ∨ p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149609104711977776593301087459 : ((p3 ∧ ((p5 → p4) ∧ ((p1 ∧ True) ∨ (((p5 ∨ (((p3 ∧ p2) ∨ p2) ∧ p4)) ∧ p4) ∨ (True ∨ p4))))) ∨ ((False ∧ p5) → (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207223777194121162377161685303 : (((((p4 ∨ p3) ∧ p3) ∨ p3) ∨ p2) → ((p2 ∨ p1) ∨ (((True ∧ ((False ∨ (p1 → (False → p4))) ∨ (p4 ∧ False))) ∨ (p2 ∧ p4)) ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696508482208013041266594850242 : (((((p2 ∧ (p2 → (False ∨ (((p3 → p1) → p3) ∨ p1)))) ∧ p2) ∧ ((p2 → (p4 ∨ p3)) ∨ (p4 → ((p4 → (True → False)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44701428368707220181988927864 : (((((False ∧ (True → p1)) → p1) ∧ (True ∨ ((p2 ∧ p4) ∧ (p2 → (p3 ∧ ((((p5 ∨ p3) ∨ p1) ∧ p5) → (p4 ∨ p3))))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741171900647375153541530841049 : ((((p4 ∨ p1) ∨ (True → (((p4 ∨ ((((((p4 ∧ p2) → (p5 ∨ p1)) ∨ p2) → p1) → False) ∨ p3)) ∨ (p2 ∧ (False ∧ p2))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_705143991547605116024663679975 : ((((((True ∧ ((p2 ∨ p2) ∧ p2)) ∨ p5) ∧ False) ∧ (((((p5 ∨ p1) ∨ p4) ∨ (((p2 ∧ p1) ∧ p3) ∧ p3)) → (p3 ∧ False)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135608672060281677688221613156 : (((False ∧ (((p3 ∨ p2) ∨ ((p1 ∨ ((p3 ∨ p3) ∧ p2)) ∧ p1)) ∨ (True ∧ p2))) ∨ (p4 ∨ (p4 → (p3 → p4)))) ∨ (p2 ∨ (p2 ∨ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40688909136627825853213477246 : (((((((True ∨ p1) ∧ False) ∨ ((p3 ∨ (((p4 ∨ (p5 ∧ p1)) ∧ p5) ∨ p1)) → p2)) ∨ ((p3 ∨ (p2 ∨ p2)) → p4)) → p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213806828135057284156821749556 : (((p3 ∧ (False ∧ p2)) ∨ False) ∨ ((p1 ∨ ((p3 ∧ ((p3 → False) ∨ False)) → ((((p3 → p4) ∨ p1) → (False → (p5 ∧ p5))) ∧ False))) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122834393805165000834954514830 : ((((p4 → ((p3 ∧ False) ∨ ((((p3 ∧ p5) → (False ∧ (True ∨ p3))) → p5) ∨ (False → p2)))) → False) ∧ ((p4 ∨ True) → p1)) → (p5 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → ((p3 ∧ False) ∨ ((((p3 ∧ p5) → (False ∧ (True ∨ p3))) → p5) ∨ (False → p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149980661347360179776766108557 : ((p4 ∨ ((p3 ∨ (p4 ∧ p1)) ∨ (p2 ∨ (p5 → ((((p1 ∧ False) ∧ False) → (True → False)) ∨ (p5 ∨ p2)))))) ∨ ((p1 ∨ (p5 → True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300693724004694123001272139840 : (False ∨ ((p2 ∨ (p4 → ((p2 ∧ p4) → (((p3 → p5) ∨ p3) ∨ (p1 → (False ∧ (False ∧ p4))))))) ∨ ((p1 ∨ ((p5 ∧ False) → False)) ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59306560579866887172862198064 : (((p4 ∨ False) ∨ (((True → (((p5 ∨ True) → p2) ∧ p5)) → ((p2 → (p5 ∨ ((p1 → (p1 ∧ False)) ∨ p4))) ∨ p5)) ∨ (p1 → p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158946092834911288228742439898 : ((p2 ∨ ((p4 ∧ (p1 → (True ∧ (p4 → (p4 → p2))))) → ((p5 → (True ∧ p1)) ∨ (p2 → p4)))) ∨ (p4 → ((True ∨ (p5 ∧ p1)) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50651376693422343277323121927 : ((((((False ∧ (((True → p2) → p3) ∧ p4)) ∨ True) ∨ p4) → (p3 ∧ (p4 ∧ ((p4 → False) ∧ p1)))) → ((False → (p2 ∨ True)) → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∧ (((True → p2) → p3) ∧ p4)) ∨ True) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692236032107645813151845276124 : ((((((p5 ∨ p4) → ((((p4 ∧ p1) ∧ (p1 ∧ False)) ∨ p2) → p5)) ∨ False) ∧ ((False ∧ p2) ∨ (((p1 ∧ p2) ∨ (p2 ∧ p2)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52068540282299465719716279435 : (((((p4 ∨ (((False → p5) → p2) → (p3 ∨ ((p1 → False) ∨ p4)))) → p2) ∧ p5) → (p4 → (p3 ∨ ((p1 ∨ p4) ∧ (False ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42972003075572495199668292095 : (((p5 → ((p5 ∧ ((False → False) → ((p2 → (p2 ∧ False)) ∧ ((((p1 ∨ False) → False) → p3) → (p3 ∧ True))))) → (p5 ∧ p3))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116164659559028854796124154605 : (((p5 ∨ (False → True)) ∧ (p4 ∧ (((p1 → (p4 ∨ p3)) → p5) → (p5 → ((p2 ∨ p3) → ((p4 → (p3 ∧ True)) → p1)))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261387960993460968135054637282 : ((p5 → p1) → ((p4 → ((((p2 → p2) ∧ ((((p4 → p2) → (True ∨ False)) → p5) ∧ (True ∨ p3))) → (p2 → p4)) → p3)) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116350049480231494804788026418 : ((((p1 ∨ p4) ∨ True) → (((((p1 → p4) ∨ (False ∧ True)) ∧ ((((True → p1) → True) ∧ p1) ∧ p3)) ∨ p5) ∨ (p3 ∧ True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608612689644234972179592918620 : ((((((((p1 → p3) ∧ (p4 ∧ p1)) ∨ (((p1 → True) ∨ (((p1 → p5) ∧ p3) ∨ False)) ∧ (p1 ∨ p3))) ∧ (False ∨ p4)) ∨ p1) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_67490605674974588006815091093 : ((p1 → ((p4 ∧ (p3 → ((p3 ∧ (p2 → ((p4 ∧ p5) ∧ p2))) ∨ p4))) ∨ (p4 ∧ (p2 ∨ ((True ∧ (p4 → p2)) → (p1 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328745815451110745627782272241 : (True → ((p3 ∨ (p2 → (p3 ∧ (p3 → (p4 → (p2 → (p5 ∨ p2))))))) → ((((p2 → True) → p3) → p2) → (p4 → ((p5 → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_48645073322162120271518961463 : (((((p1 ∧ (False → (p3 → (p2 ∨ (p2 ∧ p5))))) ∨ (p1 → (p3 ∨ False))) ∧ (p2 → ((p3 ∨ p4) ∨ p1))) ∧ ((p5 ∧ p4) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197093691879405396653649199470 : (((p3 ∧ ((p2 → (p5 ∨ p4)) ∨ p5)) ∨ p2) ∨ ((p1 → p1) → (((p5 ∧ p5) ∨ (True ∧ (False → ((p2 → p3) → True)))) ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190087417908613508014144234296 : ((((p2 ∧ (p3 ∧ (False ∧ False))) ∧ (p5 ∧ p1)) ∧ True) ∨ ((True ∨ ((p1 → (False → p5)) → (((p1 ∧ False) ∨ p4) ∨ (p5 ∧ p4)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299334287091420156893899063306 : (False ∨ ((((p4 → p2) ∨ (p5 ∨ p3)) → (((p3 → True) ∧ p4) → ((p3 → p1) ∨ ((p2 → ((p3 → True) ∧ (False → p5))) ∨ p2)))) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630712968295750616973065901588 : (((((p2 → (((False ∧ (p3 ∨ ((p2 ∨ p5) → p1))) ∧ p1) ∧ (p1 ∨ (False ∧ (True ∧ (((p1 → p4) ∨ p1) ∨ p1)))))) ∨ p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195822626155911736642374448780 : (((p4 ∨ p3) → (((p3 ∧ p4) → True) ∨ p1)) ∧ (((p5 ∧ ((p3 ∨ p5) ∨ p1)) ∨ p1) ∨ (False → ((p1 → False) ∧ (True → (p1 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23448427310570096194869033455 : ((((p3 ∧ p4) → (p1 ∨ p3)) ∧ ((((p2 ∧ ((p2 ∨ False) ∧ False)) ∧ False) ∧ ((((False ∧ p4) ∨ p3) → (False ∨ p3)) → False)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809746849306615581514527276630 : (((p5 → ((((False ∧ p3) ∧ (p2 ∧ (p3 → (False ∨ (p2 ∧ ((p3 → p2) → (p5 ∨ (p2 ∨ (p4 ∨ p3))))))))) ∧ p1) ∨ (False → p4))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243402544961878852777361422561 : ((p5 → True) ∧ ((p3 ∨ (False ∧ ((((((True ∨ True) ∨ p3) ∨ False) → (True ∧ ((True → (p4 ∨ (p1 → True))) ∧ False))) ∨ p2) ∧ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248199229324086415527577415039 : ((p2 ∨ p1) ∨ (((p1 ∨ p2) → ((((p3 ∧ (True ∧ p3)) ∨ False) ∨ p4) → (False ∨ ((p4 ∧ ((p1 ∧ p5) ∧ (False ∨ p2))) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200825593619073194626224019984 : ((p5 ∧ (p4 ∨ (((p2 → p1) → True) → p1))) → ((((p4 ∧ p2) ∨ ((p1 ∧ p4) → p3)) ∨ (p1 ∧ (p5 ∨ (p2 ∨ (True ∨ True))))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 → p1) → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303816006801337907459351345059 : (p1 ∨ (((p1 ∨ (((True ∧ (p3 ∧ (False → ((((p5 ∨ (False ∨ p1)) ∨ p5) ∨ (p3 → (False ∨ p2))) ∧ p2)))) ∨ p3) ∨ p2)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50491527076854013388961104124 : (((p5 → ((((p4 ∧ ((p3 ∧ p1) → p2)) → True) → ((p3 ∧ True) ∧ (p2 → (p2 ∧ p3)))) ∧ p3)) ∨ (True ∨ (p5 → (p3 ∧ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



