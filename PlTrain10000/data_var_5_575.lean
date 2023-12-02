variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38526801308824402661664955357 : (((((p3 ∧ p3) → (((True → p1) → (p4 → (p5 ∧ True))) ∨ p2)) → (False ∧ (((p4 ∧ p1) ∧ (True → p3)) ∨ (p3 ∧ p5)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750484927383555025582460596266 : (((True ∧ ((((False ∨ ((p5 ∨ (p2 → (p5 ∨ True))) → (p2 → (True ∨ p4)))) → p3) ∧ ((p1 → p2) → p1)) → (p3 ∨ (p1 ∧ p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((p5 ∨ (p2 → (p5 ∨ True))) → (p2 → (True ∨ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204948298415911365748885816720 : ((((p2 → p2) → (p3 → True)) → p5) ∨ (p2 → (p5 → ((p1 ∨ (p3 ∧ (((True ∧ (False ∧ False)) ∧ False) ∨ p1))) ∨ ((p3 ∧ p4) → p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174201445563619074654867660895 : (((((p5 ∨ p5) → ((p5 ∨ True) → ((p3 → False) ∨ p2))) ∨ True) → (p3 ∨ p4)) → ((p1 → (True ∧ (p4 ∧ p3))) ∨ (p1 ∨ (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115418737478362375011195483478 : ((((((p2 → p3) ∧ False) → (False → False)) ∧ p1) ∨ (((((p1 ∨ False) → p1) ∧ (p1 ∧ ((p4 ∨ p5) ∨ p5))) ∨ p3) ∨ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476771292809515914207280911733 : ((((p4 ∧ (p4 ∧ (p1 ∨ (p4 ∨ (p2 → (p4 ∧ p4)))))) ∨ ((((p4 ∧ (p1 ∧ False)) ∨ (p2 ∧ p1)) ∨ (p5 ∧ (True ∧ p2))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56221044991907275669453303096 : (((p2 ∨ (p5 ∨ (False ∨ p5))) ∨ (p4 → (((((False → ((False → p4) ∧ p1)) ∧ p4) → p4) → (p4 ∨ p2)) ∧ ((p4 → False) → p5)))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117083679271741977103015824446 : (((False → p3) → (((p5 ∨ (True ∧ (p1 ∧ ((p1 → (p5 ∨ (p5 ∨ ((False ∧ p2) → True)))) ∨ p4)))) ∧ (p1 → p3)) ∨ False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345562576520793384585602582733 : (p3 → (((((True → p5) ∨ p3) ∧ p3) → ((p4 ∨ p4) ∨ (p1 ∨ (p5 ∧ ((p3 → (p3 ∨ (p3 → False))) ∨ (False → (p4 → p2))))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799875771765766563382608281426 : (((p1 → (p5 → ((((p5 → p3) ∧ (p2 ∧ (((((p1 → ((p3 ∨ p5) → False)) ∧ p5) ∨ p3) ∧ True) ∧ (p5 ∨ p5)))) ∧ p4) ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319024713559017333545612452190 : (p4 ∨ (((((p3 → (False ∨ (True ∨ (p5 → ((p5 ∨ False) ∨ False))))) ∨ False) → (p1 → (p3 ∧ p3))) ∧ p3) ∨ (True ∨ ((False ∧ p1) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657674295831413076509339332062 : (((((p5 ∨ p3) → (((p1 → (False → p4)) ∨ ((p5 ∨ ((p5 → p5) → (p2 → (p1 ∨ p5)))) → (p5 ∧ p1))) → False)) ∨ (False → False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261400761397771895698911196539 : ((p5 → p1) → ((((p1 ∨ p2) ∧ p3) ∨ (True ∨ (p1 → p1))) → ((False → p5) → ((((p5 → p5) ∧ ((False ∨ p4) ∧ p3)) ∨ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809690068790867396529794231681 : (((p5 → (((((p5 → ((p5 ∨ p3) ∧ p2)) → p4) → ((p5 ∨ (((False → p5) → True) ∧ p5)) ∧ p2)) ∨ (False ∨ False)) ∧ (p5 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307332231751397701077446425620 : (p1 ∨ (p3 ∨ (((p1 ∨ p5) ∧ p4) ∨ ((p2 ∧ (p3 → p5)) → ((((p3 ∧ ((p4 ∧ (p4 → (True ∨ p3))) ∨ p3)) ∨ p3) ∨ False) → p5))))) := by
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
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h18 := h16 h17
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81105553031673272244454985965 : ((((True ∧ (p3 → True)) → (((p1 → ((p1 → p2) → p5)) ∧ (True ∧ p4)) ∧ (p4 → ((p4 ∨ True) ∧ p4)))) ∧ ((p3 → p2) → p3)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ (p3 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327135773166635623196551750653 : (True → ((False ∧ ((p2 → p5) ∧ (((p4 ∧ (((p4 ∨ ((p4 → True) ∧ p3)) → (False ∨ ((p5 → p2) → False))) → p3)) ∧ p3) ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158655856408611871049464263904 : ((p1 ∧ (False ∧ ((p5 ∧ (True → (p5 ∧ True))) → ((p4 → ((p1 ∧ p4) ∧ (False → p5))) ∧ p2)))) ∨ ((False → True) ∨ ((p3 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52022313262557765060920561034 : (((False ∨ (((True ∧ ((p4 → p1) ∨ True)) ∨ p1) → (p2 → (p3 → (p5 ∨ p1))))) ∨ (((p5 ∨ p5) → (p5 ∨ p2)) → (True ∨ p4))) ∨ p4) := by
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
theorem thm_5_vars_301910046347347786265160384385 : (False ∨ ((p3 ∧ p1) → ((((((p2 ∧ p1) ∨ ((p2 ∨ p5) → p4)) ∨ p4) ∧ (((p3 ∧ p5) ∧ True) ∨ p5)) ∨ False) ∨ (p2 ∨ (False → p5))))) := by
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
theorem thm_5_vars_817044115818769484419002117462 : ((((((True → False) → (p3 → ((((((True ∧ True) ∨ (p5 → p1)) ∨ (p1 ∨ p3)) → (p4 → p4)) → (p4 ∨ p5)) ∨ True))) → p2) ∧ p1) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True → False) → (p3 → ((((((True ∧ True) ∨ (p5 → p1)) ∨ (p1 ∨ p3)) → (p4 → p4)) → (p4 ∨ p5)) ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804856417408996803910747625875 : (((p3 → ((True → True) ∧ (((p4 → p1) → (True → (p3 ∧ True))) → ((((False ∨ False) → False) ∧ p3) ∧ (((p2 ∧ p2) ∧ p4) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137868838955464846082681251403 : ((p3 ∨ (True → (p1 ∧ (((((p5 ∨ p5) ∧ p5) ∧ ((p3 ∧ False) → p2)) ∧ ((p3 ∧ False) → p4)) ∧ (p2 → p1))))) ∨ ((p2 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631235096196514456819442557035 : ((((((((((p1 ∧ ((p3 → p5) ∧ p3)) ∧ p5) ∧ (p2 ∨ p2)) ∧ (False ∨ (False → p5))) → (True → (True ∨ False))) → p4) → p4) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177876374017112436250927889829 : (((((((p5 ∨ ((p2 ∨ False) → True)) ∨ p4) → p4) → True) → p4) ∨ True) ∨ ((((p1 ∧ (p5 ∨ (p1 ∧ False))) → (p2 ∧ p2)) → True) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346774322127768133030679027737 : (p3 → (((p2 → (True → ((True ∧ (False ∨ ((((p4 → (p1 → p4)) ∧ True) ∨ p3) ∧ p1))) ∧ p2))) → False) ∨ (p4 ∨ (p2 → (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37865016266296664917082140586 : ((((p3 → (p2 → (False ∨ (p2 → ((p4 → (p3 ∧ p5)) ∧ ((((p1 ∨ p2) → (False → p1)) ∨ (False ∨ p2)) → p4)))))) → p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190785713455098154110551074301 : (((((False → p4) ∨ (True ∨ True)) → False) ∨ (p2 ∨ False)) ∨ (True ∧ ((((p2 → (p4 → p1)) → (p5 → p1)) ∨ ((p5 ∧ False) → p4)) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145223176318999718504001944121 : (((p5 ∨ (p2 ∨ (False ∧ (p4 ∨ (p3 ∧ p4))))) ∨ (False → (p3 ∨ (False ∧ (((p4 ∧ p1) → p1) ∧ True))))) ∧ (((p2 → p2) ∧ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40305335015651525962948133608 : (((((((((p1 ∨ (p2 ∧ p2)) → (False → True)) ∧ ((p2 → ((p3 → p1) ∨ p2)) ∨ p4)) → p1) ∨ (p1 → p4)) ∧ p1) ∨ False) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63910959091622749806448007231 : ((False ∨ ((p2 ∧ (((p2 ∨ (((p1 → p3) ∨ (p3 ∧ True)) ∧ (p5 → (False ∨ (p2 ∧ True))))) → p3) ∧ ((p3 → False) → p5))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214602094872747878167064907402 : (((p5 ∨ False) ∧ (p4 ∨ False)) ∨ (p5 ∨ ((((p2 ∨ (True → (p5 ∧ p4))) ∧ False) ∨ False) → (p2 ∧ ((p4 → ((p4 ∨ False) → False)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55908999406777799847084515141 : (((p5 ∨ ((True ∨ p3) ∨ p4)) ∧ ((((((True ∧ (p2 ∧ True)) ∨ p1) → p5) ∧ p3) ∧ ((p3 ∨ False) ∧ False)) ∨ (p1 → (p3 ∨ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705267763058301233944724736123 : (((((True → ((p4 → True) → (p3 ∧ False))) ∧ p2) ∧ (((p2 → ((True ∨ p3) ∧ ((p5 → p2) ∧ (p1 → (p4 ∨ p2))))) ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346668507475523165866052442409 : (p3 → (((p1 ∨ (p4 ∧ ((p3 → ((p1 → ((p3 ∧ True) ∧ ((p4 ∨ p1) ∨ p4))) → p5)) ∨ p3))) ∧ (p3 ∨ p5)) → ((p3 → False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h18 := h3 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h20 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h21 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h22 := h3 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h24
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639752920841210307000018691143 : (((((p5 → (p2 ∧ p2)) ∧ (((p2 → p4) ∧ (p3 ∨ True)) → (False ∨ ((((p4 ∧ False) ∧ ((p5 ∨ p3) ∧ p5)) → p1) → False)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799982302496572184693617936778 : (((p2 → (((p2 ∧ ((((p3 ∧ p4) ∨ p1) ∨ (False ∨ (((p5 ∨ p1) ∨ p2) ∨ p2))) ∨ (p1 ∨ (False ∧ (p1 → False))))) → p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342165045581213845270461137512 : (p2 → ((((p4 → p4) ∧ (p4 ∧ p2)) → ((((False ∨ p5) ∧ (p1 → p5)) ∧ (p5 → p4)) ∨ (p1 ∨ p3))) ∨ ((p2 ∨ (p5 → p3)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309780187008305159933172696786 : (p2 ∨ (((p2 ∧ (True → (p2 ∨ (p2 → (False ∧ ((((p2 ∧ p4) → False) ∧ p3) → (p3 → p1))))))) ∧ p5) ∨ (((p3 → False) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179563323243704661977426539167 : ((p2 → (((p2 ∨ True) → ((((p5 ∧ p3) ∧ p5) ∧ p2) → True)) → False)) ∨ ((p5 ∧ p1) → ((p4 ∨ (False → True)) ∨ ((p1 ∧ True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264539941005138957009484225702 : (True ∧ (((p5 ∨ p2) ∧ p3) ∨ (p2 → ((((p3 ∨ ((False ∧ p3) → (p1 ∧ (True → p5)))) → (p1 ∨ True)) ∧ p4) ∨ ((True ∨ False) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44351210602051912460386854705 : ((((False ∨ (p2 → ((((p4 ∧ False) ∧ True) ∧ (((True → True) ∨ p2) ∧ False)) ∧ False))) → ((False → (False → (False ∨ p5))) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203099320333906416383349196975 : (((p2 → p3) → ((False → True) ∨ p3)) ∧ (((p1 ∧ ((((p5 ∧ p1) ∨ p1) ∨ (False → (p3 ∧ (True ∨ (p4 → p3))))) → False)) ∨ True) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136239976672120981084675083907 : ((((p5 ∧ p5) → ((True ∧ p3) → False)) ∨ (((p2 ∨ (True → ((True → p2) → ((p5 ∧ p1) ∧ True)))) ∨ p3) → False)) ∨ ((False ∧ p4) → p2)) := by
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
theorem thm_5_vars_262228946962644943569239702747 : (True ∧ ((((p5 → (((((p4 ∨ p1) → ((p4 ∧ (p5 ∨ False)) ∨ False)) ∧ ((p2 ∧ p3) ∨ False)) → False) → False)) → p2) ∨ (True ∨ p5)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68610117167730409626235727096 : ((p4 → ((((p2 → (p5 ∨ p3)) ∧ (p2 ∨ ((p2 → ((False → (p3 ∨ (p3 → p2))) ∨ p5)) → (p3 ∧ p4)))) → (p1 ∨ p1)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179330746411777853206570910507 : ((p1 ∨ ((((p2 ∧ True) → False) ∧ (True ∨ (p2 ∨ False))) ∧ (p3 ∨ False))) ∨ ((p4 ∧ (((p3 → (p1 ∧ True)) ∧ p4) → p5)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190715100270636298038157733270 : (((((p4 ∧ p4) ∨ p1) ∧ (p3 ∨ p3)) ∧ (p1 ∧ p2)) ∨ (p4 → (False ∨ (True ∧ (p4 ∨ ((p4 ∧ ((p3 ∨ p2) → (True ∧ p3))) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657497509834989543643180207461 : (((((p2 ∨ False) ∨ (p4 → ((((False ∨ p5) ∨ (False ∧ True)) ∨ (((p3 → (True ∧ p5)) ∧ p2) → (p5 → False))) ∧ p2))) ∨ (p4 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314347370057666996336594104806 : (p3 ∨ ((True → (((p3 → (p1 → True)) ∧ p1) ∧ (((False ∨ False) ∨ ((True → ((False ∨ p4) → p4)) → p1)) ∧ p5))) → ((p1 ∨ p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164856107985608094015353512580 : (((False ∨ (p4 ∧ (p4 ∨ ((True ∧ ((((True ∨ p2) ∧ False) ∧ p3) ∧ p2)) ∧ True)))) ∨ True) ∨ (True → ((((False ∨ True) → p5) ∧ p1) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43659186469456691829880772042 : (((((False ∨ ((((p5 → ((p1 ∧ p2) → p1)) ∨ (p1 → p4)) ∨ p4) ∨ ((p2 → p5) ∨ True))) → (p1 ∨ (True → False))) → p2) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345417195245191483076576728763 : (p3 → ((((p4 ∨ p2) ∨ (p4 ∨ (False ∨ (True ∧ (False → ((p3 ∨ (p5 ∧ True)) ∨ (False ∨ ((True → (p2 → True)) ∧ p3)))))))) → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208140824027325317565596674391 : ((((p4 ∧ p2) → p2) → (p2 ∧ False)) → (p2 ∧ ((((p1 → (p1 → ((p5 ∧ p5) ∨ (p3 ∧ p3)))) ∧ False) ∧ ((p1 ∨ False) ∨ False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∧ p2) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52751371077021466486701215219 : ((((p5 → (True → ((p1 → ((p1 ∨ p3) ∨ p3)) ∧ (p3 ∨ p4)))) ∨ False) → (((p4 → False) ∨ (True ∨ (p1 ∧ p3))) ∨ (p4 → p3))) ∨ p4) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84086806260754009583040219638 : ((((p4 ∨ (False → ((True ∧ p3) ∧ True))) → (False ∨ (True → ((True → p1) ∧ False)))) ∧ (((False ∧ p2) ∨ (p2 → (p1 ∨ p5))) ∧ True)) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ (False → ((True ∧ p3) ∧ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201094697074277344880627090625 : ((True → (((p4 ∨ p2) ∧ (False ∧ p2)) ∧ p1)) → (p2 ∧ (((p1 ∧ (False ∧ p2)) ∨ ((p3 ∨ p1) ∨ (True → (p4 ∧ p3)))) → (False ∧ p3)))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- We need to get the left conjuct of h23 based on <expert-advice>.
        let h24 := h23.left
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h29 := h1 h28
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- We need to get the left conjuct of h31 based on <expert-advice>.
      let h32 := h31.left
      -- False on the left can always be used.
      apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- False on the left can always be used.
    apply False.elim h36
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h43 := h1 h42
        -- We need to get the left conjuct of h43 based on <expert-advice>.
        let h44 := h43.left
        -- We need to get the right conjuct of h44 based on <expert-advice>.
        let h45 := h44.right
        -- We need to get the left conjuct of h45 based on <expert-advice>.
        let h46 := h45.left
        -- False on the left can always be used.
        apply False.elim h46
    case inr h47 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h48 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h49 := h1 h48
      -- We need to get the left conjuct of h49 based on <expert-advice>.
      let h50 := h49.left
      -- We need to get the right conjuct of h50 based on <expert-advice>.
      let h51 := h50.right
      -- We need to get the left conjuct of h51 based on <expert-advice>.
      let h52 := h51.left
      -- False on the left can always be used.
      apply False.elim h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41222955299027002701857388031 : (((((((p3 ∨ (True ∧ (p5 ∧ p4))) ∧ p5) ∧ (False → (p4 ∨ False))) ∨ ((p3 → p5) ∧ p4)) ∧ (True → ((False ∨ p4) ∧ p1))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194951238106750311432804566290 : ((((p3 ∨ p4) ∧ ((p1 ∧ p4) ∧ p3)) → p3) ∧ (((p5 ∧ (p4 ∨ (p4 ∧ True))) ∨ (False ∨ False)) ∨ ((p5 → ((p1 ∨ True) ∨ p3)) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h14
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241346309810973978583874809964 : ((False → False) ∧ (((p5 → ((False → (p1 → (p5 → ((p3 ∧ (True ∨ p2)) → False)))) → p3)) ∨ ((p1 ∧ (p5 → False)) → p3)) ∨ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809688389374751815678398679814 : (((p5 → (((True ∧ ((p5 ∧ (p1 ∧ p2)) ∨ (p2 → (p3 ∨ (p3 → (False → ((p2 → p1) ∧ p4))))))) ∧ (False ∧ False)) ∧ (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213284242232285384570186850318 : ((((p1 → p5) → p4) ∧ True) ∨ ((p1 ∨ ((((p1 → p2) → (((p5 → p4) → ((p3 → p3) → (p3 ∧ p4))) ∨ p1)) ∧ True) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136484526188007259820921406393 : ((((p5 ∨ p1) ∨ p1) ∧ (((p1 ∨ (((((p4 ∨ False) → p1) ∨ p3) ∧ p2) ∧ p1)) ∧ p2) → ((False ∨ p1) ∨ p2))) ∨ ((p2 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114074223013270244175937418757 : (((((p4 ∧ (p3 ∧ p2)) ∨ p4) ∨ (p5 ∨ ((True ∨ False) ∨ ((p1 → ((p1 ∧ False) ∨ p3)) ∧ p5)))) ∨ (p3 → (p2 ∨ p2))) ∨ (p2 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_658376695096182964015405635526 : ((((False ∨ ((p3 ∨ (((p2 ∨ p5) ∧ (p3 ∧ (False ∨ ((p5 → True) → (p4 ∨ p5))))) → p2)) → ((p3 ∨ p5) → p4))) ∨ (p1 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_119370303573133287743130677393 : ((p3 → (p2 ∨ (((False → ((p1 → (True → True)) ∨ ((p3 ∨ (p4 ∨ True)) → p3))) ∧ p3) → (((False → p1) → p1) ∨ True)))) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_205155317447438109406639560270 : (((p1 ∧ (p5 ∧ p3)) ∧ (True ∨ p3)) ∨ (p2 ∨ ((p4 ∧ ((p2 ∧ p4) ∨ p1)) ∨ ((((p5 ∧ p3) ∧ p5) → True) ∨ ((False → p2) → p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322359440124730561038915093345 : (p5 ∨ (((True → (p4 ∨ ((((False → p3) ∨ (p2 ∧ (((False → False) ∧ (False ∧ p2)) → False))) ∨ False) → p2))) ∨ ((p4 → p4) → True)) ∨ p1)) := by
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
theorem thm_5_vars_312314707947998021068361873825 : (p2 ∨ (p2 → ((p1 ∨ (p2 ∧ ((p1 ∧ (p5 ∧ p3)) ∧ True))) ∨ (True ∨ ((((((p1 ∨ p5) ∨ p2) ∧ False) → p3) → (False ∨ p1)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64678804150091901849365490819 : ((p1 ∨ (p3 ∨ ((p1 ∨ p3) → ((p5 ∨ p5) → ((p4 ∨ (p3 → (p2 ∧ ((((p2 → False) ∧ p5) ∧ (p2 → p1)) → p3)))) ∨ True))))) ∨ p5) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165083740947404459790011828599 : (((False ∨ (False → (((p4 ∨ (p2 ∧ p4)) → (p1 → ((p5 ∨ True) → False))) ∨ p3))) → p1) ∨ ((True ∧ (p4 ∨ p3)) → ((p4 ∨ p3) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712846986233672014592771387743 : (((((p2 ∨ p2) → (p2 ∧ (p3 → p4))) ∨ ((((p4 ∨ p4) → ((p2 ∧ True) ∧ (p1 ∧ (p5 ∨ (p3 ∧ True))))) ∧ (p5 ∧ p2)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_173828782490276701889684026589 : (((p4 ∨ (((p2 ∨ p3) ∧ (((p1 → p1) ∧ p2) ∨ p2)) → (False → p3))) ∨ p2) → ((p5 ∧ p5) ∨ (p1 ∨ (((p4 → p5) ∧ False) → p4)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300890366081590714637748055456 : (False ∨ ((p5 ∨ (((((p1 → (p4 ∧ p4)) ∧ p5) ∨ p5) → p3) ∨ (True ∧ False))) ∨ (((False ∧ (p2 → p5)) ∧ (p4 ∨ p3)) ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720379386943062890066942833222 : ((((((True ∨ p1) → True) ∨ p2) → (False ∨ (False ∨ (p1 ∨ (((p2 → p3) ∨ (False → ((p4 → True) → True))) ∨ ((False → p5) ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48947991787018806898270631248 : ((((False ∧ ((p4 ∧ p1) ∧ ((False ∨ (p5 → True)) ∨ (p3 ∨ (((False ∧ (p3 ∧ False)) ∨ True) ∧ p5))))) ∧ False) ∨ (True ∨ (p3 → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669829169369834751838373837276 : (((((((p5 ∨ (p1 ∨ p4)) → (False ∧ True)) → ((True → True) ∧ p1)) ∧ (((p5 ∧ True) → p1) ∧ (p1 ∧ p2))) ∨ ((p4 → p3) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263492776361313278379971128052 : (True ∧ ((p5 ∨ (((((p3 ∨ p5) → (((p4 ∧ False) ∧ True) → ((p2 ∧ p4) ∨ p1))) ∧ p5) ∧ p2) → (p1 → False))) → ((True → False) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111695064516127616199854008695 : (((((((p4 ∧ p4) ∨ ((p3 → p3) → True)) ∧ ((False ∧ (((p2 → (p1 ∨ p2)) → False) ∧ p1)) ∨ False)) → p3) → p4) ∨ True) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172065814738270379385253399679 : ((((False ∧ ((((False ∨ (p2 ∨ p5)) → p3) → p5) ∧ p2)) → p5) → (p2 → p5)) ∨ ((((p4 ∧ (True → (p1 ∨ p1))) ∧ p2) ∧ False) → p3)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249179840182122404783467543553 : ((p4 ∨ p3) ∨ ((((False → ((p2 ∨ p3) ∨ p3)) ∧ ((((True ∨ p5) ∧ p4) → (True → (False ∨ p5))) → (p3 → p2))) ∧ p5) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314803055523705683333129844993 : (p3 ∨ ((((False → ((p4 ∨ p4) ∨ (True ∧ p4))) → True) ∨ (True → p3)) ∧ ((((p2 ∧ p5) → True) → (False ∧ p4)) ∨ (p4 → (True ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179221870376954808363929779895 : ((p4 ∧ ((p3 ∧ False) ∧ (p5 ∨ (((p4 ∨ True) ∧ p5) ∧ (p1 ∨ p4))))) ∨ (((p4 ∧ (True ∨ p3)) → (p1 ∧ ((True ∧ False) ∧ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787527665632691449733557070221 : (((p4 ∨ (False ∨ (p4 ∧ ((((p4 ∨ (p5 ∧ (p2 → p2))) → ((p3 → p2) → (False → (p3 ∨ p1)))) ∧ p3) ∧ (p4 ∨ (p2 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254828535223674533854434578032 : ((p3 ∧ p5) → ((((p3 ∧ (p2 → p4)) → p4) → (((p2 ∨ True) ∧ p2) ∨ (((p1 ∧ p4) → (p4 ∨ p3)) ∧ (p1 ∧ True)))) ∨ (p1 → p1))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319202118598869593815022545495 : (p4 ∨ (((((((((p2 → p1) ∨ p2) ∨ (p4 ∧ p2)) ∨ p1) ∨ True) ∨ p4) → p1) ∧ (p2 → p1)) → (p2 ∨ ((p3 ∨ (p5 ∨ p4)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357304781852748295542714754056 : (p5 → ((p2 ∨ p4) ∨ ((((p1 ∧ (p1 ∨ p3)) ∨ p4) → ((p4 ∧ True) ∨ False)) → (((p1 → p5) ∧ ((p4 → p3) ∧ False)) ∨ (False → p4))))) := by
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
theorem thm_5_vars_119537943489197612044239919040 : ((p5 → ((p5 → (((((((p3 → True) → ((p2 ∨ p1) ∧ p1)) ∧ (p1 ∧ (True ∨ p5))) → p5) → False) → True) ∧ p3)) → p3)) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131487781344745486185277747969 : (((p3 ∧ (False ∨ (p3 → p5))) → ((p2 → False) ∨ ((False ∨ (((p1 ∨ p2) ∨ (p2 ∨ p3)) ∨ False)) ∨ (False ∧ p2)))) ∧ (True ∨ (False ∧ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797111037659702392809129228771 : (((p1 → (((p2 ∨ (True → p1)) → (((p1 ∧ (False ∨ (p3 ∧ (p5 → (p3 → p4))))) ∧ ((False → p3) → (p3 ∧ True))) → p4)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615357544044290519538846626973 : ((((((p4 → (((p5 ∨ False) ∧ p2) ∧ True)) ∨ ((p1 → (p1 → p5)) → (p5 ∧ p5))) ∨ (p5 → (((True → p1) ∨ p4) ∧ p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340194563662010495847206179109 : (p1 → (p4 → (p2 ∨ (p3 ∨ (((p3 ∨ p1) → (p1 ∧ ((p5 ∨ (((p4 ∧ (p2 ∨ (p5 ∨ False))) → p4) ∧ True)) → (False ∨ p1)))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321705315104954761790710802060 : (p4 ∨ (p4 → (True → ((((p5 ∧ (True ∨ p5)) ∨ (p3 ∨ p2)) ∨ p1) → (((p2 ∧ p5) → (((p5 → (p4 ∧ True)) ∧ False) ∨ p4)) ∨ p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52729193253364821786767495427 : ((((p2 → ((p4 ∧ (p3 → (((p5 → p3) → p1) ∧ p2))) ∧ p5)) ∧ p5) → (((True ∧ (False ∧ p2)) ∨ ((p4 → False) ∨ p1)) ∨ p5)) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303046769601351014787110063144 : (False ∨ (p2 → ((p4 ∨ (p1 ∨ (((False ∨ (False ∨ (False ∨ p5))) ∧ ((False ∧ (p4 → p1)) ∨ (p5 ∨ ((p4 ∨ False) ∧ p2)))) ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254378569926333429498741648736 : ((p2 ∧ p4) → (True → (((p3 → False) ∨ ((p3 ∨ (False ∨ ((p1 ∨ (p5 ∧ True)) ∨ (p5 → (p2 ∧ p5))))) → (p4 → (p5 ∨ p5)))) ∨ p4))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2550088210372834320680683400 : (((p3 → ((p1 ∨ p4) → (True → p1))) → p3) ∨ (((False ∨ ((p3 ∧ (True ∨ True)) ∨ ((False → (p1 ∨ p3)) → True))) ∨ False) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228414088731810106274620928887 : ((False ∨ (p2 ∧ p1)) ∨ ((True → ((p1 ∧ False) ∧ p1)) → (((p1 ∧ ((((True → p5) ∧ p3) ∧ p4) ∧ (False → p4))) ∨ (False → p2)) → p2))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679457152772018753685618414524 : (((((((((p1 → (((True ∧ (p3 ∧ p3)) → p2) ∨ (p4 ∧ p4))) → p5) ∨ p5) ∨ p2) ∨ p3) ∧ p3) → (((p4 ∨ True) ∧ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206052451994938839967441181088 : ((p2 ∧ (p3 → (False ∨ (p3 → p1)))) ∨ ((((p5 ∧ ((True ∨ p4) ∧ (False ∨ ((True ∨ p2) → p4)))) ∨ p4) ∧ p4) ∨ ((p2 → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



