variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113307237807744765857241719963 : ((((((p4 ∧ p1) ∧ p4) ∨ p2) ∨ (p2 ∨ ((p5 → False) ∨ (False → (((p4 → p3) → p5) ∨ (p2 ∧ p2)))))) ∧ (False ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768600347704376021739570288700 : (((p5 ∧ ((p5 ∨ ((p1 ∨ ((True → p5) → ((p1 ∨ p1) ∧ (p5 → p3)))) → p3)) → ((p1 ∨ (p5 ∨ (p1 → False))) ∨ (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612303756421262399034812099829 : (((((p1 ∧ (((((p3 ∨ p5) → p2) → p3) → (p1 ∨ (((p4 ∨ (p2 ∨ p5)) ∧ (p3 ∧ p1)) ∧ p1))) ∧ p2)) ∧ (p5 ∧ False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306031339337405645061268063534 : (p1 ∨ (((p4 ∧ (p1 ∨ p1)) ∧ p3) → ((((((p5 ∨ p5) → (p3 ∧ True)) ∨ (p2 ∨ p5)) → ((p2 → p5) → p3)) ∨ p3) → (False ∨ p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184830985317403431659116621653 : ((((p5 ∧ False) ∨ (False → p3)) → (p5 ∧ ((p3 ∧ p3) → p5))) ∨ (False → ((p1 ∨ p5) ∨ ((p1 ∧ (True → True)) → ((False ∨ True) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47514863902971732888563273061 : (((p2 ∨ (p4 ∨ (((p3 → (((False ∨ True) → ((True → p5) ∨ (p3 → p3))) → ((p3 ∧ p1) ∧ False))) ∧ p1) → p5))) ∨ (p5 → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679232289318929572176558656524 : ((((True → ((True ∧ ((p4 ∨ (p1 ∨ True)) ∨ p3)) → (p3 ∧ ((p2 → p2) ∧ ((False ∧ p3) → False))))) ∨ ((p3 ∨ (p1 → p2)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_308385065485982330796507307525 : (p2 ∨ ((((p1 ∧ ((p3 → (True ∨ (p1 ∧ (p4 ∧ (p4 → p2))))) ∧ p4)) ∧ (((p4 ∨ p2) ∨ ((False ∧ True) → p3)) → p1)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305516363578999686153029425173 : (p1 ∨ ((p5 → (((((p2 ∨ p4) ∧ (p5 → p2)) ∨ (p5 → False)) → p2) → p4)) ∨ (((p2 ∧ (True → p1)) ∨ (p4 → (True ∨ False))) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153008195387965341575692189302 : ((p2 ∧ (((((True ∧ ((p3 ∨ p3) → (((p2 ∨ p5) ∧ p5) ∧ (False ∧ True)))) ∧ p3) ∧ True) ∨ False) ∨ p1)) → (((True ∨ p4) → p4) ∨ p2)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263573469451946948661352391322 : (True ∧ (((p5 ∨ (p2 ∨ (p1 → True))) → ((p1 ∨ ((p5 ∨ p3) ∧ (((p4 ∧ p3) ∧ True) ∧ p2))) ∧ p5)) ∨ ((p2 ∨ (p1 ∧ True)) ∨ True))) := by
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
theorem thm_5_vars_227287074761244182924978821705 : (((p1 → p4) → p5) ∨ ((False ∧ (False ∨ True)) ∨ (((p2 → (p2 ∧ (p4 ∧ (((p2 → p3) ∨ p3) ∧ p1)))) ∧ p3) ∨ ((p2 ∨ p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758881815975773900442747089277 : (((p2 ∧ ((((((p1 ∧ False) → (p1 ∧ ((p1 ∨ False) → ((p5 ∧ False) → p5)))) ∨ p2) → ((p4 → p3) → False)) ∧ (p5 → p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152549404106751218052596270383 : ((((p5 ∧ False) → True) → ((True ∧ p5) ∧ (((p3 → ((p2 ∨ p1) → ((p1 ∨ False) ∧ p4))) ∨ p1) ∨ False))) → ((p2 ∨ (p5 ∧ True)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ False) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 ∧ False) → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156702137951563735526576752742 : ((((p2 ∨ ((((((p2 ∧ p4) ∨ p2) → p2) ∨ False) → p2) ∨ True)) → (True ∧ (True → p4))) ∧ p2) ∨ ((p4 ∧ (True ∧ False)) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67523999420314297938894353264 : ((p1 → (((p3 ∧ (p2 → False)) ∧ p2) ∧ (((p2 → (p4 → ((p5 ∨ p2) → p3))) → p3) ∧ ((((p4 ∧ p2) → True) ∧ p2) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631109444257380473799904318129 : (((((((p1 ∨ p1) → (p5 → ((((False ∨ p3) ∨ (p3 → p4)) → ((False → False) ∨ (p2 → (p3 ∨ p3)))) ∨ p5))) ∨ p4) → p4) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336437948800074173700133107001 : (p1 → ((p3 ∨ ((p1 ∨ (p3 ∧ False)) → (False ∨ (((True ∧ True) ∧ ((p1 → (True → p4)) ∨ (p5 ∨ (True ∧ (True ∧ p5))))) → p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137437048449335899179747750789 : ((p4 ∧ (((((p4 ∧ p4) ∧ (False → (p2 ∨ p3))) ∧ p4) → ((p2 → (True → p5)) → False)) ∨ ((False ∨ p1) ∧ p3))) ∨ ((True ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136050928014969740297820325601 : ((((False ∧ (True → (p1 ∨ (p3 ∨ p4)))) ∧ p1) ∧ (p1 ∨ ((p4 ∨ ((p1 ∨ (p4 ∨ False)) ∨ False)) ∧ (p1 → p5)))) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_53357917775167979611674818376 : (((((p1 ∧ (p4 → (p1 ∨ (p4 ∨ p3)))) ∨ (False → p4)) ∨ p2) → (p3 ∨ ((p4 → p4) → (p4 ∨ (False ∨ ((True ∨ p2) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187091861946624267851350783367 : (((p3 → p2) ∧ (p4 ∨ (p4 ∧ (p5 ∨ (False → (p5 ∧ p4)))))) → ((((p5 → (p2 ∨ True)) → p3) ∨ (p5 → (p2 → (p4 → p2)))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324266858641659436786314230290 : (p5 ∨ (((p4 → (p5 ∨ p2)) → ((p4 ∧ p1) ∨ p2)) ∨ ((p1 → (p3 ∨ (p3 ∧ (p2 ∧ (p1 → (True ∧ ((True ∨ p4) ∨ p2))))))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54234240666557684763509371543 : ((((False ∨ ((p3 → p5) → (p4 ∧ False))) → False) ∧ (True ∧ ((p4 ∧ p5) ∨ ((((p3 → p3) → (p5 → False)) → (p1 → True)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315284639015924116417909690881 : (p3 ∨ (((p4 ∨ (True ∧ p2)) ∨ p3) → (True → ((p5 ∧ (p1 → p5)) ∨ (True ∨ ((False ∨ ((p5 → (p4 ∧ (p2 ∧ p3))) ∧ p2)) ∨ p3)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54678331942894035619723145911 : ((((((p3 → True) → False) ∧ (True ∨ False)) → p3) → (p5 → ((((p3 ∨ (True ∨ (p1 ∨ True))) ∨ p5) ∧ (p1 ∧ (True ∨ True))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87584728688983572663283789386 : ((((True → (False ∧ False)) ∨ (p3 ∧ False)) ∨ ((False → True) → ((True → ((p1 ∨ p5) ∨ ((True ∨ p2) → (p4 → (p3 ∧ True))))) ∧ p4))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347035075693229498441042644510 : (p3 → ((((p3 ∧ (((p5 ∧ p2) ∨ True) ∨ (p5 ∨ (p4 ∨ (p4 ∨ p3))))) ∧ p5) ∨ p2) → ((False ∧ (True ∧ (p5 → p5))) ∨ (False → True)))) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h27
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47214747763889942964706397734 : ((((p4 ∧ ((((p5 ∧ (p3 ∧ True)) ∧ p5) ∧ True) ∧ p5)) ∨ (p4 ∧ (p5 → (p1 → (p3 ∨ (p5 ∨ (p5 ∨ p5))))))) ∨ (p5 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117551881568801105693379572392 : ((p2 ∧ (((p3 ∧ (True → (p5 ∧ p3))) → (False ∧ ((p4 ∧ False) → (p2 ∨ p1)))) → ((((p1 ∨ p3) ∧ p1) ∧ p1) ∧ p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179049080001891614167157465135 : (((p3 → True) → (((p3 ∧ (False → (p3 → p4))) ∧ (p4 ∧ p5)) ∨ False)) ∨ (False → (p4 → ((p4 ∧ ((True ∨ False) ∧ (p4 → True))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199088800050384989308665766378 : ((((p5 ∨ (p3 ∨ (p2 ∧ p1))) → p4) ∧ p3) → (((((p2 → (((True ∨ (p1 → False)) → p1) → p4)) ∧ p3) → p2) ∨ p1) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799748593672301843129636457304 : (((p1 → (p1 → (p3 ∨ ((((p3 ∧ p5) → (((False ∨ (((p2 → p5) → p1) → p1)) ∧ ((True → p1) → p5)) → False)) ∨ p4) ∨ p1)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48174450260176313248121620198 : ((((p2 → p3) ∧ ((p2 → (p3 → (p1 → p5))) ∧ (False → (True ∨ ((((p1 → (p5 ∨ True)) ∧ p2) ∨ p4) ∧ p3))))) → (p4 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310344925800095039471569426883 : (p2 ∨ ((False → ((p2 ∧ (p3 ∨ ((p5 → p5) ∧ p3))) → p2)) → (p1 → ((p2 ∧ (((p5 → p4) → (p3 ∧ (True → p5))) ∨ p2)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52097069314484474413296537542 : (((((p5 → (p5 ∨ p4)) ∧ (((p1 ∨ (p3 → (p4 ∧ p3))) ∨ True) ∨ p5)) ∨ False) → ((p1 ∧ (p2 ∨ p1)) ∨ (p2 ∧ (False ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56377304741931948735774988013 : (((((p1 → False) ∧ p5) → False) → (((True ∧ (((True ∧ (p3 → (False ∨ p1))) ∨ ((p2 ∨ p5) ∧ p4)) → (p4 ∨ p2))) → p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706974161017108349573862604209 : ((((((p5 → p4) ∧ ((False ∧ p1) ∨ p4)) ∨ p5) ∨ ((p3 → ((((False → p4) ∨ ((p5 ∧ p1) ∨ (p4 ∨ p1))) → p1) ∨ p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185043555230065687668546618438 : (((p3 → p1) ∧ ((p4 → p3) → (((p3 ∧ p3) ∨ p3) ∧ p1))) ∨ ((True ∨ ((p1 → p3) ∧ (p5 ∧ ((True → True) ∨ p5)))) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657223251566453632326819718305 : ((((((p1 → False) → p3) → ((((p4 ∧ (p1 ∨ (p2 ∨ (p5 → ((False ∧ p2) ∨ p2))))) ∨ (p1 ∧ p3)) ∨ p5) ∧ p2)) ∨ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63111565391588037210721385915 : ((p5 ∧ ((((True ∨ (p5 ∨ p2)) ∧ ((p1 ∧ ((p2 → True) ∨ p3)) ∨ (((p2 → (p3 → True)) ∨ p1) ∧ (p3 ∧ True)))) ∧ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56260396619465092243480099095 : (((p2 → ((p2 → False) ∧ p3)) ∨ (((p2 ∨ (((p1 ∨ p5) → (True → ((True ∧ p4) ∧ p2))) ∨ p3)) ∧ p5) → (p2 ∨ (p4 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197031073831735042103708845540 : (((((p5 → False) → p4) → (p3 ∧ p3)) ∨ p2) ∨ (False → ((((((p3 ∨ p2) ∧ (p4 ∨ p4)) ∧ (True ∧ p2)) ∨ p1) ∧ True) ∧ (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304245091741010116447766489795 : (p1 ∨ (((p1 → ((p3 → p4) ∨ (False ∨ ((p3 ∨ p5) ∨ (((((p2 ∧ p4) → (p1 ∧ p4)) ∨ (p4 ∧ p4)) ∨ True) → p1))))) → False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p3 → p4) ∨ (False ∨ ((p3 ∨ p5) ∨ (((((p2 ∧ p4) → (p1 ∧ p4)) ∨ (p4 ∧ p4)) ∨ True) → p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67289819960114272083906469686 : ((p1 → (((((((p1 ∨ (p4 ∧ (True ∧ (((p1 ∨ p2) → ((False → p4) ∨ p5)) ∨ p5)))) → p3) ∧ p5) → p4) → p3) → p4) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61185865972441594838426956669 : ((False ∧ ((p4 ∨ p5) ∧ (p1 ∨ (((((p1 → False) ∨ (p1 → ((p3 ∨ p1) ∨ True))) → p1) ∨ p5) ∨ ((False ∧ p3) ∨ (p3 ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213436125376323794459060993948 : (((p4 ∨ (p1 ∨ True)) ∧ p4) ∨ ((p1 ∨ p1) ∨ (((((True → p4) → True) ∨ (p1 ∨ ((p3 ∧ (p3 → p3)) ∧ (p5 ∧ p1)))) ∧ False) → p3))) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- False on the left can always be used.
      apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300705641005528568888968923532 : (False ∨ (((p3 ∨ (p1 → ((p3 → True) ∧ ((p3 ∨ (((p3 ∨ p1) ∨ p1) → True)) ∨ p1)))) ∨ p1) → ((True ∨ p1) → (p5 ∨ (True ∨ p1))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117618640557967049962782256318 : ((p3 ∧ (((p3 ∨ (True ∧ (False → ((((False → p5) ∧ False) ∧ (p1 ∧ p2)) → (((p1 → p1) ∨ p5) ∨ p4))))) → p5) ∧ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307139985811583998944889396602 : (p1 ∨ (False ∨ (((((False ∧ (p2 ∨ p5)) → ((False → True) ∨ (True → p1))) → p2) ∨ (p5 ∨ p2)) → (((p3 → True) → (p1 ∧ p2)) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395872960677298631947404200720 : ((((p3 ∧ ((p1 → (((((p2 ∨ p2) → p5) ∧ p5) ∧ False) ∧ p4)) → (((p2 → (((p2 ∧ True) ∧ p4) ∨ p1)) ∨ p2) ∨ True))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_51362531376285600453340894116 : (((((p2 ∧ p1) ∨ (p2 ∨ (((p4 ∧ p3) ∧ (True ∨ p1)) → (True ∨ (p5 → p5))))) ∧ p1) → (p1 ∧ ((p2 → False) ∧ (False → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40847142405269066400917624185 : ((((p5 → ((False ∧ True) → (((p3 ∧ p2) ∧ ((False → ((False ∧ (True ∧ p3)) ∧ (True → (True ∨ False)))) ∨ p4)) ∧ p1))) → p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157007030144811283119983979865 : ((((p5 ∨ (p3 ∨ p3)) ∧ ((p5 → (p1 → p5)) → (p5 ∧ ((p4 → (p1 ∨ True)) ∨ p2)))) ∨ p3) ∨ ((((p1 → p4) ∧ p3) ∧ p3) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173739395314085725913595833389 : (((((((p5 ∨ p1) → p4) ∨ False) ∧ p2) ∧ ((p2 → p1) ∨ (p3 → p2))) ∨ True) → ((p5 ∧ p2) → ((False ∧ (True ∧ False)) ∨ (p2 ∧ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315759903439192864559613348111 : (p3 ∨ ((True ∧ p5) → (((p2 ∨ p2) → (p2 → ((p1 ∨ p3) ∨ (((p4 ∨ p3) → True) ∧ (p3 ∨ (p2 → p2)))))) ∧ ((p4 ∧ True) → True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53918931269693587702121643476 : (((p2 ∨ ((((p4 → False) ∨ p4) ∧ (p3 → p4)) ∧ p1)) ∨ (p5 ∨ ((((p2 ∧ (True ∨ (p4 ∧ p2))) ∨ (p1 ∨ p3)) ∧ True) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658174396791132066724550737443 : ((((p4 ∧ (p4 ∧ ((p4 ∨ ((((((p3 → p3) ∧ False) ∨ (True → (p2 ∨ p2))) → p5) ∨ (p2 → p1)) → p5)) ∧ p2))) ∨ (False → p3)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_314480543244286806822867837335 : (p3 ∨ ((True ∧ (p3 → (p3 → ((p4 → False) ∨ ((p4 → ((p3 → p2) ∨ p3)) ∨ ((True → p3) ∧ True)))))) → (p1 ∨ (p2 ∨ (True ∨ True))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167500205486558959101149997816 : (((((p3 → (p1 ∨ p5)) → ((p2 ∧ p3) ∨ (p2 → p5))) ∨ (p3 → p2)) ∧ (p3 ∨ True)) → (p3 → ((((False ∨ p2) ∨ p1) ∨ False) ∨ True))) := by
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
    cases h4
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245330493479411000493352076935 : ((p2 ∧ p2) ∨ (True → (p3 → ((p1 ∨ (((((p2 ∧ ((p5 ∧ p1) → p3)) ∧ p5) ∧ ((True ∨ False) ∧ p2)) ∨ p3) → (p1 ∨ p5))) ∨ True)))) := by
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
theorem thm_5_vars_243429425845458217512770665567 : ((p5 → True) ∧ (((p2 ∨ p3) ∧ p2) ∨ ((((((p1 → p2) ∧ (p1 ∧ (((p3 → p2) ∧ (p2 → p1)) ∨ True))) ∨ False) → False) → p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330255309022640298085837536494 : (True → (False ∨ ((((p4 ∧ p2) ∧ ((p3 → False) ∨ p3)) ∨ ((p4 ∨ (p2 → p4)) ∧ (p5 ∧ p1))) → ((p4 → True) ∧ (False ∨ (True ∨ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h13.left
      let h19 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157805469348763878088598015190 : ((((((p2 ∧ p2) ∨ (p1 ∨ (p2 ∨ p2))) → (p4 → p4)) ∧ True) → (((p5 → False) ∨ p3) ∨ p2)) ∨ (p1 → ((p2 → p2) ∨ (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80406280141590689632201190283 : (((((p4 → ((True ∨ (p1 ∨ (p4 ∧ False))) ∨ p2)) → False) → (p5 ∨ (p1 ∧ (False ∨ ((p2 ∨ p2) → (p5 ∨ p2)))))) → (True ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((True ∨ (p1 ∨ (p4 ∧ False))) ∨ p2)) → False) → (p5 ∨ (p1 ∧ (False ∨ ((p2 ∨ p2) → (p5 ∨ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p4 → ((True ∨ (p1 ∨ (p4 ∧ False))) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177700341884272539030047003599 : ((((False → (((p3 ∧ (p1 ∨ p5)) → p1) ∨ p3)) ∨ (False → p5)) ∧ p4) ∨ ((p4 → p4) → (((p2 ∧ ((p3 → p4) ∨ True)) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40350212710356936077110705474 : (((((((p4 ∨ p4) ∧ (True ∧ ((p3 → (((p2 → ((False ∧ p5) ∨ p4)) ∨ p4) ∧ True)) ∨ (False → p1)))) ∧ p2) → False) ∨ p5) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304121365144516432213977951223 : (p1 ∨ ((p4 → ((True → (p2 ∧ (p4 → False))) → ((p3 ∨ (((p5 ∧ p1) → False) → p3)) → (((p2 ∧ p2) ∧ (p2 ∨ False)) → False)))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41390036259567947668758692776 : (((((p4 ∧ (True → ((p3 ∨ p2) ∧ p2))) ∧ ((False ∧ p1) ∧ (p5 ∨ True))) ∧ ((p5 ∨ (True ∧ p5)) ∨ (p3 ∧ (p5 ∧ p5)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140209173174490302191807582742 : ((((p2 → p5) ∨ (((((((p4 ∧ ((p1 ∨ p2) ∧ p3)) ∨ False) ∨ p2) ∨ p4) ∧ p4) ∨ False) ∧ True)) → (p4 ∨ True)) → ((p4 ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680326720172239551908816828082 : (((((((False ∨ ((False ∨ (p2 ∨ p4)) → (p5 → p1))) ∧ True) ∨ (p5 ∧ p1)) ∨ ((False ∨ True) ∧ p3)) → ((False ∨ p5) ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123682912786889994623059685422 : (((True ∨ ((p1 ∧ (((p5 → True) ∨ p4) ∧ False)) → ((False ∧ (p2 ∧ p5)) ∧ p1))) → (((False → (False ∨ p5)) ∨ False) ∧ False)) → (p5 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p1 ∧ (((p5 → True) ∨ p4) ∧ False)) → ((False ∧ (p2 ∧ p5)) ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617411484273489038856297659 : (((((p1 ∧ (p3 → p4)) ∧ ((p3 → (True → (p4 ∧ (p2 ∧ (False ∨ True))))) ∨ ((False ∧ True) ∨ False))) ∨ p2) ∨ (p4 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112570742546363486212896922826 : ((((p3 ∨ ((False ∨ (True ∧ p1)) ∨ (((((p4 ∧ False) ∨ (True → p1)) ∧ p4) ∧ p2) ∧ (True → (p4 ∧ p4))))) → p1) → False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309364100035186461371273570732 : (p2 ∨ (((p1 ∧ ((p3 ∨ p3) ∨ p5)) ∨ (p1 → (p2 → (((p5 ∧ False) ∧ ((p5 ∨ p3) ∨ False)) ∨ ((p3 ∨ p3) ∨ False))))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111049169012061039280035072691 : ((((((p2 → ((p1 ∨ p5) → ((True → p5) ∧ (p5 ∧ (p2 → False))))) ∨ p1) ∨ True) → ((p1 → p4) ∨ (p4 ∨ False))) ∧ p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137992222463735144559057821377 : ((p5 ∨ (p3 ∧ (p3 ∧ (((((p5 → True) ∧ True) → False) → p5) → (((p1 ∧ p4) → (p5 ∨ (False ∧ p2))) ∧ p5))))) ∨ ((p5 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158051160962453232094328714035 : ((((p4 ∧ True) ∨ (p1 ∧ (p1 ∨ p4))) ∨ (((True → False) → False) ∨ ((True ∧ (p5 → True)) ∧ p2))) ∨ (((p3 → p4) → (True → True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228883125005782656357243442350 : ((p4 ∨ (p1 ∧ p4)) ∨ ((p3 ∨ (((p5 ∧ p5) ∨ (p2 ∨ (True → p2))) ∧ (p1 → p4))) ∨ (((True ∨ p5) ∧ (p1 → (p2 → p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710418238789056074198973300585 : ((((((p4 → True) ∧ (p5 → p1)) → p5) ∧ (((p1 → (p1 → False)) ∧ (((p3 ∨ p4) → p3) ∨ p5)) ∨ ((p1 ∧ (p3 ∨ p4)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57096307783709347991285145822 : ((((p4 ∧ p5) ∧ p4) ∨ (((p3 → False) → ((False ∨ p1) ∨ ((((p1 → (p2 → p5)) → (p1 → p1)) ∧ (False → p3)) → p1))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165032732696524590481507928236 : (((((p3 ∧ p4) → p2) → (((p1 → (p1 ∧ (p1 → p1))) ∧ (p3 ∨ p2)) ∧ p1)) → p1) ∨ ((((p3 → (True ∧ True)) → False) → False) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (True ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118877806929282270422689674824 : ((True → ((p1 → p5) ∨ (((False ∧ ((((p2 ∨ p1) ∧ p2) → (p2 → p5)) → ((p5 ∨ p5) ∧ p3))) ∨ (p4 → p4)) ∨ p5))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352138052481137393517357016004 : (p4 → ((((True ∧ p1) ∨ (p3 → p2)) → p1) → ((True ∨ (False → p3)) ∧ ((p5 → ((p2 ∨ (True ∧ p5)) ∧ (False ∧ p2))) ∨ (True → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172931287219817973915673200863 : ((p3 ∧ ((((True ∧ False) ∧ (True ∨ (p3 ∨ ((p2 ∨ p5) ∧ p4)))) → p3) → False)) ∨ ((p3 → ((((p1 ∨ p1) ∧ p3) ∨ True) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_171454011808099261315965014724 : (((p3 ∧ (True → ((((False ∧ False) ∨ p1) → (p5 → (False → False))) → p5))) ∧ p5) ∨ (((p5 ∨ p3) ∨ (True ∧ (False ∨ (p4 → p4)))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161472715725900023184507994125 : ((p3 ∧ (((False → True) ∨ p5) ∨ (p5 ∧ (((True ∨ p5) → True) ∧ ((p2 ∨ False) → (p5 ∨ False)))))) → ((True → p2) → ((p4 → p5) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40319862671906555866910119024 : (((((p4 ∨ (((p4 → ((False ∧ True) ∨ True)) → ((True ∧ p1) ∨ (False ∧ (p1 → (p3 ∨ (p1 → False)))))) ∨ True)) ∧ p3) ∨ p4) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705099439136017198144938777753 : ((((p5 → ((p1 → (p4 ∨ p4)) ∨ ((True → True) ∧ False))) → (((p5 ∨ p1) → ((p2 ∨ True) ∧ (((p2 → p1) → False) → p4))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117317893120036536627100326695 : ((False ∧ ((p4 ∧ (p2 → (((p4 → True) → p5) ∨ ((False ∧ p1) ∧ p4)))) ∨ ((p3 ∨ ((p4 ∧ p2) → (p5 ∨ True))) → p3))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152232813696640518179070905097 : (((p3 → ((p2 → (p2 ∨ True)) ∨ True)) ∧ (p1 ∧ ((p3 ∧ p5) → ((False ∨ ((p5 ∧ False) ∨ True)) ∨ p3)))) → (p1 ∧ ((p3 → p2) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341024692102499570136647446704 : (p2 → ((p4 ∧ ((p1 → (((((p4 ∧ (p2 ∧ p1)) ∧ p4) ∧ (p2 ∧ p3)) ∨ ((p3 ∧ (p2 ∨ p3)) ∨ (p1 → p5))) ∧ p4)) ∨ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729739585543212858074158091527 : (((((p3 → p2) ∨ p1) → (((((((p2 ∧ ((False → (p1 ∨ p1)) → True)) ∧ ((p3 → False) → True)) ∧ p1) ∧ p1) ∧ p1) ∨ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226248635089273003342729047139 : (((p3 ∨ p2) ∨ False) ∨ (p5 ∨ (p2 → ((False ∨ ((p4 → (p1 → True)) ∧ (((p3 → p4) → p4) ∧ ((p5 → (False ∧ p1)) ∧ p5)))) ∨ True)))) := by
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
theorem thm_5_vars_390446817113357884034062188617 : (((((((((p4 → p3) ∧ False) → p5) → False) ∧ p2) ∧ (p4 → (p2 ∨ ((((p5 → p4) ∧ (p5 → (True ∨ True))) ∧ True) → p5)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_38732901199956450261706929627 : ((((p4 ∧ (p2 → ((True → False) → p4))) → (p3 → (((p2 ∨ ((p1 ∧ p4) ∧ p2)) → (((p3 → p5) → p1) → p1)) ∧ p2))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152643425868957677167877445376 : (((p5 ∨ p3) ∧ ((((True ∨ p4) ∨ True) ∧ ((p3 → ((p3 ∨ True) ∨ p4)) ∧ (p1 → p5))) ∨ (p4 → True))) → ((True → (p2 ∧ p5)) ∨ True)) := by
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
          let h10 := h7.left
          let h11 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h7.left
          let h14 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h22.left
          let h26 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h22.left
          let h29 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h22.left
        let h32 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h33 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47555379091925201120603714301 : (((True → ((((p5 ∧ p2) → False) ∨ p4) ∧ (p2 → ((p3 ∨ (p2 ∧ p5)) ∨ ((p4 ∧ (p4 ∨ p2)) ∧ (True ∨ False)))))) ∨ (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300094061541538884055333069318 : (False ∨ (((((True → p3) ∨ ((((p2 ∧ p5) ∨ False) → (p4 ∨ (p2 ∨ (p5 → p4)))) ∧ p5)) → False) ∨ (p2 → (False ∨ p4))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115315174904733682124532480999 : ((((p5 ∨ ((p5 → p3) ∨ p4)) ∨ ((True ∧ p4) → p3)) → (True → (((p3 ∨ ((p3 ∧ p2) ∨ False)) → (True ∧ True)) → p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



