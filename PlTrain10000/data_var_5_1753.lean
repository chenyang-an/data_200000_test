variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314260380826070570936148797301 : (p3 ∨ (((True ∧ (True ∧ p3)) ∧ ((p2 ∨ p3) ∨ (False ∧ ((p3 ∧ p1) ∨ (((p5 ∧ (False ∧ p2)) ∨ p4) ∧ True))))) ∨ (p5 → (p3 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47144684422747324971090775715 : (((((p3 ∨ (p2 ∧ (((True → ((p1 ∨ p2) ∨ p3)) → (p5 → p2)) → p2))) ∨ p5) ∨ ((p1 ∧ p4) → (p2 → p4))) ∨ (p3 ∧ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49779823391024912955839818651 : (((p3 ∨ ((p2 ∧ ((p2 ∨ False) ∨ (((p3 ∧ True) ∨ ((p1 ∧ ((True → p4) ∨ p4)) ∨ p1)) ∨ True))) ∧ p4)) → (p5 ∨ (False ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687860405708213318802221306663 : ((((((p4 → (((p1 ∨ False) → p5) ∨ (p3 → p5))) ∨ False) ∨ ((p5 → True) → p1)) ∧ ((p2 ∨ ((p3 ∧ p3) ∧ (False → p1))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249687467485045599967105866165 : ((p5 ∨ p4) ∨ ((False → p4) ∧ (((((p4 → p5) ∧ ((p3 → (p3 ∨ False)) ∧ (p2 ∨ (p1 ∧ ((True ∨ True) ∨ False))))) → True) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231289334615129681946596473634 : (((p5 ∨ p2) ∨ p3) → (p3 ∨ ((True → (p4 ∨ p4)) ∨ ((p4 → (p5 → p5)) ∧ (((p3 ∧ False) → (True ∨ (True ∧ (p4 ∧ True)))) ∨ p1))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499236518745385260024046043385 : (((((p2 ∨ p5) ∧ p3) ∨ (((p4 ∧ (((p4 ∧ ((p5 ∨ True) ∨ p1)) ∨ p3) ∨ p3)) ∧ (False → p3)) ∨ ((True ∨ (p3 → p4)) → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949249154519197502052419923614 : (((((p3 → p2) ∧ p2) ∧ (((p1 → p2) ∧ p3) ∧ ((False ∧ (p5 ∧ ((p3 ∨ ((p2 ∧ (p3 ∧ (p2 ∧ True))) ∧ p4)) ∨ p5))) → True))) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113633627671209531551653700501 : (((p4 → (((p5 ∨ (p5 → p2)) ∧ (p4 → (p2 ∨ ((p2 ∨ p1) → False)))) ∧ (p1 ∨ ((p2 ∧ p3) ∧ p4)))) ∨ (p2 ∨ True)) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149469793786803260771678701777 : ((False ∧ ((p5 ∨ p3) ∨ (False ∨ ((False ∨ ((((p3 ∧ p4) ∨ ((False ∨ p1) → p4)) ∧ p5) → p5)) ∨ p3)))) ∨ (p5 → (p2 → (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232243257602807330150947844814 : (((p1 → p4) → p1) → ((((((p1 → True) ∧ (p2 ∧ p3)) ∧ (p4 ∨ ((p2 ∨ p1) → p1))) → (p1 ∧ p4)) ∨ False) ∨ (False ∨ (False → p1)))) := by
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
theorem thm_5_vars_164464658879498812658555459402 : (((((False ∨ ((False → (p2 → p5)) → (p4 ∨ (False ∨ (p3 → False))))) ∧ p4) ∨ p5) ∧ p3) ∨ ((True ∨ p2) ∧ ((p5 ∧ False) → (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_177892680671522851893579310475 : (((((((False ∨ p1) ∨ p4) ∨ (True ∨ p4)) ∧ p3) ∧ (True ∧ True)) ∨ p2) ∨ (p3 ∨ (p4 ∨ ((p5 ∧ False) → (True → (False ∨ (p1 ∨ p3))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199854226322072827680312136724 : (((True ∨ (p4 ∧ (p5 → p1))) ∧ (p5 ∨ p1)) → (p2 ∨ (p1 → ((p3 ∨ ((False → p1) → ((True ∨ False) ∨ p3))) ∨ (p1 ∨ (p1 ∨ p3)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614717058938052838782716486771 : ((((((p1 → ((False → (((p2 → p1) ∨ False) → (False ∨ p1))) ∧ (p5 → (p2 ∧ p2)))) → p1) ∨ ((True ∧ True) ∨ (False → True))) ∨ p4) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214528336777889549922987472396 : (((p5 ∧ p2) ∧ (False → p2)) ∨ ((p2 ∨ ((p1 ∧ p5) → (False → (p2 ∧ p2)))) ∧ (p2 ∨ ((p5 ∨ ((p4 ∧ (p1 ∨ p4)) → p4)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65654512505667141248794053207 : ((p4 ∨ ((p2 ∨ (((p4 → True) → ((p5 ∧ p3) ∧ True)) ∧ (((((p5 → True) → p3) ∨ ((p2 → True) ∨ p2)) ∨ p2) ∨ False))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112150647451672259688943037929 : (((p1 ∧ (p5 → (True → (p2 ∧ ((p5 ∧ True) ∧ ((False ∨ p4) ∨ ((((True ∧ (p2 ∨ p3)) → p2) ∧ p5) → p3))))))) ∨ True) ∨ (p4 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219590893130820334507459855876 : ((True → (p5 ∧ (p1 ∧ p4))) → (False ∨ (((True ∧ (((p4 ∧ p4) → p1) ∧ (False ∧ False))) ∨ (p5 ∨ (p4 → p4))) → ((p5 → p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54926818754510267890036586105 : ((((True ∧ (p4 ∧ (p1 ∨ p4))) → False) ∧ (((p4 ∨ p4) ∨ (((True ∨ ((p3 ∨ p1) → ((p5 → p3) → p4))) ∧ p5) ∨ p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329477593331280059984221214452 : (True → ((False → p5) ∧ (False ∨ ((p5 ∨ ((False ∧ ((p2 ∨ (p3 ∨ p5)) ∧ p5)) ∧ p5)) ∨ ((p1 ∨ p4) → ((True ∧ (False ∨ True)) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729001947511088159774024675460 : (((((p2 ∨ p4) ∧ p2) → (((p1 ∧ p1) ∨ (((True ∨ False) ∧ p1) ∧ True)) ∨ (False → ((p2 ∨ ((p3 → p5) ∧ False)) → (p5 → p1))))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119109409038251685521580258625 : ((p1 → ((True ∨ True) ∧ (((((p3 ∨ p4) ∧ True) ∧ (p3 → p5)) → p2) ∨ (p2 ∨ ((((p1 ∧ p5) → False) ∨ p2) ∨ True))))) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_204826460926626386534805444375 : ((((p4 ∧ (p3 ∧ False)) ∨ p3) → p4) ∨ (((p1 ∨ ((((p3 → p1) ∨ p5) ∨ (p1 ∧ p4)) ∧ p5)) ∧ p4) → ((True ∧ p2) ∨ (p3 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790269319004297188871743650834 : (((p5 ∨ (p1 ∧ (p1 ∨ ((p1 → (p3 → (p1 ∧ ((((p3 → False) ∧ ((True ∧ p5) ∨ False)) ∧ (p5 → p4)) ∧ p4)))) ∧ (p2 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181049577284599807655885721290 : (((p1 ∧ False) → (p5 ∨ ((((p1 ∧ p1) ∧ False) ∧ (p2 → p5)) ∨ p3))) → ((p1 → (True ∨ p4)) ∧ (p2 → ((p5 → False) → (p5 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115790919425782537258647576939 : (((((False ∧ p5) ∨ p2) ∨ p4) ∧ (((p2 → (True → (p1 ∨ ((False → False) → (p3 ∧ p1))))) → ((True ∨ p1) ∨ p4)) → p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191767942629676225693122338217 : ((p1 ∨ (((p4 → p4) → (p4 ∨ (p2 ∨ p4))) → False)) ∨ (p4 → (False → (((p3 ∧ ((p2 ∧ p1) ∧ ((p2 → False) ∨ p4))) ∨ p3) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112575427006602949483202656639 : ((((p1 → (((p1 → (p3 ∨ ((p5 ∧ ((p3 → p1) → (p5 ∨ (p3 ∧ p4)))) ∨ (p3 ∨ True)))) → p3) ∨ p5)) → p1) → p5) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150387468549253513216240754565 : ((((((((p3 ∨ p2) → (p5 ∧ p5)) ∨ p2) ∨ p2) ∨ (((False → p2) ∧ (False → False)) → p2)) ∧ p4) ∧ True) → ((True → (p4 → False)) ∨ True)) := by
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
theorem thm_5_vars_59252676624145661722404918866 : (((p2 ∨ p4) ∨ (False ∧ (((((((p3 ∧ p4) ∨ False) → p1) ∧ ((p3 ∧ (p5 ∨ False)) → True)) → p3) ∧ p4) ∧ (p3 → (p3 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50920413597729656391380197620 : ((((p2 → (((p4 ∨ ((p2 ∨ ((True → False) ∨ p4)) ∨ False)) ∧ p5) → p3)) → (False ∨ p5)) ∧ (p4 → (((p5 ∨ p5) → p1) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654174945362461357524527333629 : (((((((((p2 → (p5 ∨ True)) ∧ ((p3 → False) ∧ p3)) ∨ (p4 → p5)) ∨ ((p2 → p4) → (False ∨ p1))) ∨ p3) ∨ True) ∨ (False ∨ False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_317830573100993699533014440666 : (p4 ∨ ((((p4 → p2) ∨ True) ∧ (p5 ∨ ((((True ∧ ((p4 → p5) → p5)) ∨ p4) ∧ p5) ∨ (((False ∧ (p4 → p4)) ∧ p3) → p5)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656738805107955934301283519908 : (((((((p2 ∧ True) ∧ p2) → (p3 ∧ p3)) ∨ ((False ∨ (((False ∧ p4) ∧ (True ∨ (p2 ∧ (True → True)))) ∨ p4)) ∧ p2)) ∨ (p1 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_125463721875913031905752982720 : (((True ∨ p5) ∧ ((p5 ∨ ((False → p2) ∨ p1)) ∧ ((p1 ∨ (p5 → (p1 ∧ ((p4 ∨ p3) ∨ ((p4 → p5) ∨ p3))))) ∨ p5))) → (p1 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
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
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
        case inr h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135681982886316201249560223049 : ((((p4 → ((((False ∨ p1) ∧ ((p4 ∧ p5) ∧ True)) ∧ False) ∧ p3)) ∧ p4) ∧ ((p4 ∨ p2) ∨ (p4 ∧ (p1 ∧ p5)))) ∨ (p1 → (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316547954470650696263978435417 : (p3 ∨ (p3 ∨ (((True ∧ (True → (False ∨ ((False → p3) ∧ (((p3 ∨ (False ∨ (True ∧ True))) → p5) ∨ (p4 ∧ (p2 ∧ p4))))))) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299434310134265315111597268109 : (False ∨ ((False ∨ (((p5 ∧ (p4 ∨ ((True ∨ p2) ∧ ((((p1 ∨ (p4 ∧ p3)) ∧ p1) ∧ p4) → (p2 ∧ (True ∨ p3)))))) → True) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670897177443542127067843612150 : ((((p3 ∧ (((p5 → (True → p4)) → (True ∨ p2)) → (p5 → ((p3 ∧ True) ∧ ((p4 ∨ p2) ∧ (p1 → p4)))))) ∨ (p1 → (p3 → p1))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41612612320474419468012699056 : ((((False ∨ ((((p3 → p3) ∧ p4) → False) → p4)) ∨ (p4 ∨ (((p4 ∨ p1) → p2) ∧ ((p4 ∨ (p5 ∧ p5)) → (p5 ∧ False))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216995747103099148517166351002 : (((p5 → (False ∨ p3)) ∧ p1) → ((p2 ∨ (p4 ∨ ((p1 ∧ p1) ∧ (p1 ∧ ((p2 ∧ p1) ∧ (p4 ∨ ((True → p3) → (p1 ∧ p2)))))))) ∨ p1)) := by
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
theorem thm_5_vars_118739519773945864759706267198 : ((p5 ∨ ((False ∧ (p2 → (True ∧ ((False ∧ p4) ∧ False)))) ∧ (((p2 ∧ p4) ∨ (p4 ∧ p1)) ∨ (p2 ∨ ((True ∧ p1) → p5))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322503940827662221104250771977 : (p5 ∨ ((True ∧ (((p3 ∨ (((False → False) → p5) ∧ ((((False → (p1 ∨ p1)) → p1) ∧ (True → (p1 ∨ p2))) ∨ False))) ∧ p3) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61844518318818202938714994635 : ((p2 ∧ (((p2 ∨ ((((p3 ∨ p3) → (((p2 ∧ p3) ∨ p1) → (p1 ∧ ((True ∧ p2) ∧ (p4 ∧ True))))) ∧ p3) ∨ p1)) → False) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321406526489477728267549830725 : (p4 ∨ (True → (p5 → (((False ∧ False) ∨ (p3 ∨ False)) ∨ ((p4 ∨ (True → ((p1 → False) ∧ (((p2 ∧ False) ∧ p3) ∧ (p4 → p5))))) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137430623679679785783762801836 : ((p4 ∧ ((((True → (p3 ∧ (p5 ∧ (p1 ∨ (p5 → False))))) → (p4 → ((False ∧ p3) ∧ p2))) → p3) ∧ (p2 ∧ p2))) ∨ ((False ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714960686431015128655897130575 : ((((True ∨ (p2 ∧ ((p5 → p3) ∨ False))) → ((p1 → p5) ∨ (False ∧ (True ∨ (p4 ∨ ((p2 ∧ p4) → ((p1 ∨ p3) ∨ (p4 ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720737601968922119870430382779 : (((((p1 ∧ (False → True)) → p5) → (p5 → (True → (((p2 ∨ True) ∨ p5) ∧ (((p5 ∨ ((p1 ∧ (True ∨ p2)) → True)) ∨ False) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232957581889264647215166943942 : ((p3 ∧ (p5 ∨ p1)) → ((p5 → (p3 ∧ p5)) ∧ ((p2 ∨ ((False ∧ (p2 ∧ p4)) ∧ False)) ∨ ((p3 ∨ (p4 ∨ False)) ∨ (p4 ∧ (p1 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83324505972703881088021501283 : (((((False → (p5 ∧ False)) ∧ p5) ∧ ((p5 ∨ (p5 → p1)) ∨ (p4 ∨ ((p5 ∧ p1) ∨ True)))) ∧ ((p5 → True) ∨ (p5 ∧ (p1 → p5)))) → p5) := by
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
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- One of the premise coincides with the conclusion.
          exact h31
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h34 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h35.left
          let h37 := h35.right
          -- One of the premise coincides with the conclusion.
          exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191773086312185871394815251489 : ((p1 ∨ ((p5 → ((p4 ∨ False) ∨ p2)) → (p3 ∨ p3))) ∨ (True ∨ ((p5 → p3) ∧ (True ∨ (((((p1 ∨ p2) ∧ True) ∧ False) → p4) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218963166530260577298368805009 : ((p4 ∧ ((p4 → p1) ∧ p1)) → ((((p1 ∧ p3) ∨ (False ∨ (p2 → False))) ∨ (((p5 ∨ True) ∧ True) ∨ p4)) ∧ (p3 → ((p5 ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263415766754058895833525589660 : (True ∧ ((False ∧ (((p3 → ((((((p3 ∨ p2) → p3) ∧ p2) ∨ (p5 ∨ p3)) → p5) ∧ (p4 → False))) ∨ p4) ∨ p5)) ∨ ((False ∧ True) → p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42263670927507643727328372136 : (((p1 ∧ ((p4 → ((((p4 → p2) ∧ p1) ∨ (p5 ∨ p5)) ∧ (p5 ∧ (p5 → (True → ((p2 ∨ p1) ∧ p5)))))) → (p3 ∨ p5))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780872660992459238386622831161 : (((p2 ∨ (((p5 ∨ p5) ∧ p2) ∧ ((((p1 → (p1 → p4)) → p4) ∧ p4) → (((p2 → ((p2 ∨ p3) → False)) → (False → p1)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155385161962243009457043384777 : (((((p1 ∨ p5) → p3) ∨ p2) ∨ (((p2 ∧ p5) ∧ ((p1 ∨ False) ∧ ((p1 ∧ True) ∨ True))) ∨ True)) ∧ ((((p3 → p3) → p1) → p1) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788831861800751057958786500509 : (((p5 ∨ ((p5 → (((p2 → (((((((p4 ∨ p2) ∧ p2) ∧ (p3 ∧ p1)) ∧ False) ∨ p4) → (False ∨ p4)) → p3)) ∧ p5) → p3)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40826546922714405390699658368 : ((((False → ((True → (((False ∧ (p2 → (p2 → (((True ∧ False) ∨ p2) ∧ (False ∧ p4))))) ∨ p5) → (True ∧ p1))) ∧ False)) → False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49210873291414230584096205612 : ((((True ∧ p2) ∧ (((True → ((p1 ∨ False) → p2)) → False) ∧ ((True ∨ p5) ∧ ((False → True) → (p3 ∧ p1))))) ∨ (p5 ∧ (p4 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301813444799363553521314337264 : (False ∨ ((False ∨ False) ∨ ((((((p3 ∨ False) ∨ (p4 → (p5 ∨ (p2 ∨ False)))) → False) ∨ ((p3 → False) ∧ (True ∧ True))) ∧ (True → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114423768825420257709617147138 : (((False ∧ (((True ∧ p4) ∨ ((p1 → (p1 → (False → p5))) → (True ∧ (p2 ∧ p4)))) ∨ p5)) ∨ ((p2 → (p1 ∨ True)) ∨ False)) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53392841394851931812806670767 : ((((((((p5 → p4) ∨ p5) → p5) ∨ p1) ∨ p5) ∧ (True ∨ p5)) → ((p5 ∧ (False → (((False ∨ p3) ∧ p1) → p3))) → (False ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17936392086905053309908898615 : (((((p3 → (p2 ∨ p2)) → (((False ∧ p3) ∧ (p3 ∨ p3)) ∨ (p2 ∨ False))) ∨ ((p3 ∧ p3) → p1)) ∨ (p4 → ((p4 → p1) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_39668439875509633397006709310 : (((p4 ∨ (((p2 → (((p3 → ((p4 ∨ False) ∧ ((False ∧ p2) → p3))) → (((True → p2) → True) ∧ p2)) ∨ p2)) → False) ∧ p5)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51489846408688463950217162917 : (((((p4 ∨ (p5 ∨ p5)) ∧ p1) ∨ (((True ∨ p3) → (False → p1)) ∧ (p4 ∧ (False ∧ False)))) → ((p4 ∨ ((p4 ∧ p5) → p5)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172389800299402164217907406876 : (((((p1 ∨ p2) ∨ p4) ∨ (True → p2)) → (((False → (False ∧ p4)) ∧ False) ∨ p1)) ∨ ((p1 → p5) → (False → ((p2 ∨ (p3 → p3)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348176775115115484842621258081 : (p3 → ((p2 ∨ p4) → ((p2 ∨ (((((False ∨ False) → p1) ∨ p2) ∧ p2) → p1)) → ((((p5 ∧ ((p5 ∨ p3) ∨ p5)) ∨ p1) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622891742718104198700034596881 : ((((p5 ∧ (((((((p2 ∨ p3) → p1) ∧ p1) → (p3 ∨ ((p3 ∧ p2) ∧ (p2 ∨ p4)))) ∧ p3) ∧ (True ∨ False)) ∧ (p2 ∨ False))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_320012696933375866700164236722 : (p4 ∨ (((p5 ∧ False) ∧ p5) ∨ (((((p4 ∨ p1) ∨ True) ∨ False) ∧ ((True ∨ p5) ∨ (p5 ∧ (p2 ∨ (p5 ∨ ((p1 → p2) → p5)))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47251322709096215658517717787 : ((((((p3 ∧ (p5 ∧ p5)) ∨ p5) ∨ p1) ∨ (False → (((True ∨ False) → ((False → p2) → ((p1 → p2) → p3))) → p3))) ∨ (p5 ∧ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49046665896218129373992242548 : ((((p5 → (p2 → (((False ∨ False) ∨ (False ∨ p3)) ∨ ((((False → (p1 ∧ p1)) ∨ True) → p4) ∧ p5)))) → p5) ∨ (False ∨ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69026748783992019355330786426 : ((p5 → ((((((((p3 ∨ p2) ∧ p4) ∨ p5) → p2) ∨ (p4 ∧ ((p3 ∧ p5) ∨ False))) ∨ (((p3 ∨ p1) ∨ p3) ∨ p4)) ∨ p1) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189761700149015856021995573531 : ((p5 ∨ (((True ∧ False) ∧ p1) ∨ (p2 ∨ (p3 → p3)))) ∧ (p2 ∨ (p4 → (((True ∨ p3) ∨ True) ∨ (True ∨ ((p4 → True) ∧ (p3 ∨ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112876671689084774595519267234 : ((((p5 ∨ (p3 → p1)) → (((False ∨ (p3 ∧ True)) ∨ (p3 → False)) ∧ (p4 ∨ ((p2 ∨ ((p4 ∧ p5) ∨ p2)) ∧ p3)))) → p3) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626509871425790442914577374131 : ((((p4 → (((((p5 ∨ False) ∨ False) ∨ (((p5 ∨ (p2 ∨ p1)) ∧ p1) → p5)) ∨ (p2 → p4)) ∨ (False → ((p2 ∨ False) → p3)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110981188393519622980182377286 : (((((p3 ∧ (((p2 ∧ p2) ∧ (True ∨ (p5 ∨ p2))) → False)) ∨ (p2 → (((p1 ∨ p2) ∧ p3) → p4))) → (False ∧ p5)) ∧ False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430257313040329723101305788825 : (((((((False ∧ p3) → False) ∧ (p4 → p2)) → ((p4 → p4) → (((p1 ∧ (False ∧ (p4 → True))) ∧ (p5 ∧ p1)) ∨ p1))) ∨ (False → p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328417292515050473840573616915 : (True → (((((p1 ∧ (p3 → False)) → (p3 → p1)) → p1) ∧ ((((True → p1) ∨ p4) ∧ p4) → p3)) ∨ ((((True ∧ p3) ∨ False) ∧ p4) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40489578430587418013559217049 : (((((p2 ∧ p3) → (((((True ∨ (p2 → True)) → False) ∨ ((True ∨ (p3 ∨ p1)) → p5)) → (p4 → True)) → (p5 ∨ p2))) ∨ True) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126477045393491706624439191672 : ((p2 ∧ (((p4 ∨ (False ∧ True)) ∧ (p4 → (False ∨ ((p4 ∧ (True ∨ p5)) ∧ p5)))) ∧ ((((p1 → p1) ∧ p1) ∨ True) ∨ p2))) → (False ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h14 := h7 h13
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h23 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h25 := h7 h24
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Conjunctions on the left can always be decomposed.
          let h30 := h28.left
          let h31 := h28.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h29
    case inr h34 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h35 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h36 := h7 h35
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- Conjunctions on the left can always be decomposed.
        let h41 := h39.left
        let h42 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
        case inr h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
  case inr h45 =>
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- False on the left can always be used.
    apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179005068362760159536375020610 : (((p2 ∧ p1) → (((p5 ∧ p3) → (p2 ∧ False)) ∨ (p2 ∧ (p3 ∧ p2)))) ∨ (p4 ∨ ((p5 ∨ ((p3 → p1) ∨ ((p4 → p4) ∨ p2))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48348869613149148538976628343 : (((p3 ∨ ((p1 ∨ ((p1 → p3) ∨ (p5 → True))) → ((((p2 → (True → p2)) ∧ p2) ∧ p3) ∨ ((False → p4) ∧ False)))) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142280649492669702183050546626 : ((p2 ∧ ((False ∨ (p5 → True)) → (p4 ∨ (True ∧ (((False ∧ p4) → p2) ∨ ((False ∧ True) ∨ ((p5 → p3) → p2))))))) → ((p2 → False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112018648725324869440356560171 : (((((p2 → p4) ∨ p4) ∧ ((p4 → (((((p3 ∧ (True ∨ True)) ∧ ((p3 → p3) ∨ p2)) → p2) ∧ p5) ∨ p2)) ∧ p3)) ∨ p3) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46258727860022190166624162906 : ((((((False ∨ p2) ∨ (p4 → (p5 ∧ ((p4 ∧ p4) ∧ True)))) → (((p1 → p3) → p2) → (p5 ∨ p4))) → (False ∨ p5)) ∧ (p2 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228042905880107570236819049527 : ((p4 ∧ (True ∧ p1)) ∨ (((((p4 ∧ True) ∨ p3) → False) → (False ∧ p5)) ∨ (p3 ∨ ((False → ((p4 ∧ p1) ∨ ((p3 → p5) → p4))) ∨ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608087796986024788503517391826 : (((((((((False ∧ p1) ∨ p5) ∧ ((p2 ∨ False) → (False ∧ ((True ∨ ((p4 ∧ p2) ∧ (p2 → True))) ∨ p3)))) → p3) ∧ p4) ∨ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196704672810351127012325987345 : ((((p1 → (False ∨ (p3 → False))) ∨ p4) ∧ p4) ∨ (((p2 ∨ (p5 → (((p2 ∧ p4) ∨ ((p1 → True) → p5)) ∨ False))) ∨ p5) ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175085199052297473800849441083 : ((p3 ∧ ((p3 ∧ p3) ∧ (((p2 ∨ True) → (((p3 ∧ p5) ∨ p1) ∧ False)) ∧ p3))) → ((((p5 ∨ (p1 ∨ False)) ∨ (p4 → True)) → p3) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44191313426133571048440124588 : ((((((p1 → False) ∨ (((True ∨ p5) → (p4 ∨ (p5 ∧ p3))) ∨ ((p1 ∨ p3) ∧ p2))) ∨ p2) ∧ (False → (p2 ∨ (p3 → p5)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307263693347861503275840952849 : (p1 ∨ (p2 ∨ (((((p4 → p4) ∧ p4) ∨ ((p1 ∧ (False ∨ p1)) → True)) → p2) ∨ (p3 ∨ ((False ∧ (False ∨ p5)) → (False → (p2 → False))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1940687069479055116877956564 : (((((((((True → (p4 ∧ ((p3 → p3) ∨ p2))) ∨ False) ∨ p4) → p3) → p4) ∧ False) ∧ p2) ∨ p4) ∨ (p3 ∨ ((False ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625232993889906991728895821450 : ((((True → (p3 ∧ (p2 ∨ ((((False ∨ ((False ∨ p2) ∨ False)) → ((p5 → p4) → p5)) ∨ (False ∧ (p2 ∧ True))) ∨ (p2 ∧ p4))))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_678411812512117301707429224346 : ((((((p2 → False) → (p3 ∨ p2)) ∧ (p4 ∨ (((p1 ∧ (((p2 ∧ False) → p3) ∨ p3)) ∨ p4) ∧ p5))) ∨ (((True ∧ True) ∧ p3) → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_302772781602867682069402105478 : (False ∨ (p4 ∨ ((False → p2) ∧ (((((False ∧ p5) → (((p2 ∧ p2) ∧ (False ∨ (True → p2))) ∧ True)) ∨ (p5 ∧ (p4 → False))) → p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245621847089559555503445073801 : ((p3 ∧ False) ∨ ((p2 → p1) → ((True → ((p1 → (((True ∨ (((p4 ∧ True) → True) ∧ p2)) ∨ True) → (p1 ∧ (False ∨ p4)))) ∧ p3)) → p3))) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112774198649678686786812993014 : (((((False → (p3 ∨ (p3 ∨ (True ∨ p1)))) → False) ∧ (((((p4 ∨ ((False ∧ False) → p1)) ∨ p3) ∧ p5) ∨ p4) → p5)) → False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175844301215453708221201412161 : ((((p5 → ((((p2 ∧ p1) → (True ∧ p3)) ∨ p4) ∧ False)) → p1) ∨ True) ∧ ((False → ((p3 → (p5 ∨ (p5 ∧ (p4 ∧ p1)))) ∧ p1)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192627950903138437382364565435 : ((((((p1 → (True → p3)) ∧ p4) ∧ True) ∨ p2) → p2) → ((((((False ∨ p5) ∧ (p1 ∧ p3)) ∧ p2) → (p4 ∧ (p2 ∨ p3))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



