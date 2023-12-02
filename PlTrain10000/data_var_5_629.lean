variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803816748912203835164496052073 : (((p3 → (((((p5 → (True ∧ ((p1 ∨ ((False → p5) ∧ False)) ∧ ((False ∨ p3) → p4)))) → p4) ∧ p2) → (p1 ∧ False)) ∨ (p3 ∨ False))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635317332710735360218355521958 : ((((((((((p4 ∧ p3) ∧ p5) ∧ (p4 → p2)) → (p2 → (p3 → True))) → (p5 → p4)) → p2) ∧ (p4 ∨ ((True → p3) ∨ p5))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214717952028382027016810927040 : (((p1 ∧ p4) ∨ (p2 ∧ p2)) ∨ (p1 ∨ (False → ((True ∨ (p1 ∨ p4)) ∨ (((True ∨ (p5 → (p3 → p3))) → ((p5 ∧ p4) ∨ True)) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45824888521639279031398866552 : (((p2 → (((p3 → (((p3 ∨ (False ∧ p3)) ∧ p5) ∧ (False ∨ p4))) ∨ ((p2 ∨ ((p4 ∧ p5) → False)) → (p5 ∧ p4))) → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138595055287083837051697178350 : ((((p4 ∨ ((((p2 ∨ ((p1 ∧ False) ∧ ((p5 ∨ p3) → p5))) ∨ (p4 ∧ p4)) → (p3 ∧ p2)) ∧ p3)) → p5) ∧ p2) → ((p1 → p4) ∨ True)) := by
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
theorem thm_5_vars_56043609164308061789202992219 : ((((p5 → (True ∧ p1)) ∨ p3) ∨ (((((p1 → p5) ∧ (((p5 → True) ∧ ((p4 ∧ (p2 → p5)) ∧ p3)) ∨ p4)) → False) → p3) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148041316250335798997290781291 : ((((p1 → p5) → ((p4 ∧ ((p3 → p2) ∨ (p2 → False))) ∧ (((p3 ∧ p2) → p3) ∧ p4))) ∨ (True → True)) ∨ ((p4 → (p1 ∨ p3)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319643081111756098269442068770 : (p4 ∨ ((((p3 ∨ p3) ∨ p1) → (p1 ∧ (p3 ∧ True))) ∨ ((p1 ∨ (p1 ∨ (p5 ∨ (p5 ∧ (False ∧ False))))) ∨ ((False ∨ (p1 ∨ True)) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200936764562263401617471198071 : ((p1 ∨ (p2 ∨ (p3 ∨ (p2 ∧ (p4 → p3))))) → ((((p5 ∨ p1) ∧ True) ∧ ((False ∨ ((p1 ∧ ((p3 → p4) → p4)) → True)) → p4)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167795231726220824715495905265 : (((p1 → (p1 ∨ (((p3 → (p4 → (p1 ∧ p5))) ∧ p4) ∧ False))) → (p5 ∧ (False ∧ p5))) → ((p3 ∧ ((True ∨ False) ∧ False)) ∧ (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p1 ∨ (((p3 → (p4 → (p1 ∧ p5))) ∧ p4) ∧ False))) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p1 → (p1 ∨ (((p3 → (p4 → (p1 ∧ p5))) ∧ p4) ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p1 → (p1 ∨ (((p3 → (p4 → (p1 ∧ p5))) ∧ p4) ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h12
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : (p1 → (p1 ∨ (((p3 → (p4 → (p1 ∧ p5))) ∧ p4) ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h17
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702631399881573889144463669330 : (((((p3 → ((p3 → (True → False)) ∨ (False ∧ p3))) → False) ∨ (p1 ∧ (p1 → ((p2 ∨ (p3 ∧ (p1 ∧ (False ∧ (p3 → p3))))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137305449181545261992870087857 : ((p2 ∧ (((((p5 ∧ (p1 → p3)) ∧ ((p3 → (p5 ∧ (p5 ∨ True))) → p3)) ∧ p3) ∨ p4) → (p1 ∧ (p3 ∧ False)))) ∨ (p5 → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303754518146104686046926307785 : (p1 ∨ ((((p5 → ((False ∧ ((p1 → ((p2 ∧ False) ∧ p4)) ∧ (p1 ∧ p3))) ∧ ((p2 ∨ p3) ∧ (p2 ∧ (p1 → p4))))) → p1) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748525962455868001162669128483 : ((((p3 → True) → (False ∧ ((True → ((p4 ∧ p5) ∧ (p1 ∨ p3))) → (((p1 → p2) ∨ (p3 → (p5 ∧ ((p5 ∧ True) ∨ p5)))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174026636664251527492693040479 : (((False ∨ ((p1 ∨ (p2 ∨ ((False ∨ False) → (p1 ∨ True)))) ∧ (False → p4))) → p4) → ((p4 ∨ (p3 ∨ (((p3 ∨ p3) ∧ p1) ∧ p4))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p1 ∨ (p2 ∨ ((False ∨ False) → (p1 ∨ True)))) ∧ (False → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False ∨ ((p1 ∨ (p2 ∨ ((False ∨ False) → (p1 ∨ True)))) ∧ (False → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h8
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679962426221294698811814602621 : ((((((p1 → (p1 ∧ ((False → (p2 → (p2 → (p2 ∧ True)))) ∧ p2))) → ((False → False) ∧ p1)) → p4) → (((p3 ∧ p5) ∨ p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326873525031582405350246498490 : (True → ((((((False ∨ p2) ∧ (p5 → ((p2 → p1) → (((p3 → (p3 → p4)) ∨ p5) ∨ False)))) ∧ p1) ∨ ((True → p5) ∧ p3)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190403698476667330095384383370 : (((p4 ∧ (((False ∨ p1) ∨ p1) ∧ (False → False))) ∨ p1) ∨ (((p1 → p3) ∨ (True ∧ (((((p4 ∧ p2) ∧ False) ∧ True) ∧ p5) ∨ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113696482150120792335923418776 : (((((p4 → p5) ∧ ((((True ∧ (p5 ∨ (False → p5))) ∨ ((p4 → (p2 ∧ p2)) ∨ p3)) ∨ True) ∧ True)) → p1) → (False ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258884844862892388419600521483 : ((True → p2) → (((((((((p4 ∧ p1) → True) ∨ (p5 ∨ (((p3 ∨ p3) ∧ (True ∧ p4)) ∧ True))) → p5) ∨ p5) → p4) → p5) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349365348892226553621882362128 : (p3 → (p3 → ((p1 ∨ (p3 → p4)) ∨ ((p4 → p2) ∨ ((p5 ∨ (p5 ∨ (((p3 → ((True ∨ (False ∨ p1)) ∨ p4)) ∧ True) ∧ p1))) ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_830798468022725426646058218869 : ((((True → ((p2 ∧ (((((p1 → p1) ∨ ((p2 → p2) ∨ (p5 ∨ (False → p5)))) ∨ p5) ∨ p2) ∧ (True ∧ False))) ∧ (False ∧ p2))) ∧ p3) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151678057026759281776854113283 : (((True ∨ (True ∧ ((((p5 ∧ p1) ∨ (False ∧ ((True ∧ True) ∧ p2))) ∧ p2) ∨ p3))) ∧ ((p3 ∨ True) → True)) → ((p3 ∨ (p4 → False)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219280950016071273246534316195 : ((p1 ∨ (p4 → (p4 ∧ p5))) → (((((p1 ∨ (False → (((False → p3) ∧ p5) → False))) → p2) ∨ (p3 ∨ p2)) ∧ (p5 ∨ (False ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_134494766864536111637244319194 : ((((((((p3 ∧ (p1 ∨ (p3 ∨ p1))) ∧ False) ∧ p1) ∨ ((p4 ∨ (False ∧ p1)) → p5)) → (p1 → p2)) ∨ False) → p4) ∨ ((False ∨ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140485183133791996785561785845 : ((((False → (p5 → ((p4 ∧ (True → (p1 ∧ (p2 → (p1 ∧ p2))))) ∧ True))) ∨ p1) ∧ ((False → (p1 ∧ False)) ∧ p3)) → (p2 → (p1 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355529652333063166292930357478 : (p5 → ((((p3 ∨ ((p3 → p4) → (((p5 ∨ True) → (p4 ∧ (p2 ∧ ((p1 → True) → True)))) ∧ p5))) ∨ (p5 ∧ False)) ∧ p1) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260878427222663683119141727551 : ((p4 → True) → (p1 → ((((p4 ∧ ((p4 → ((p3 ∧ True) → p5)) ∨ ((p3 ∧ (False ∨ False)) → p1))) → p2) ∧ p4) ∨ ((p1 ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198912439485804995055276928946 : ((p3 → (False ∧ ((True ∧ p3) ∧ (p2 ∧ p4)))) ∨ ((False ∧ ((((True ∨ p2) ∧ ((p5 → True) → True)) ∨ (p1 → p2)) → False)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215416981014574757170965662409 : ((p3 ∧ ((p2 ∧ p2) ∧ True)) ∨ ((((p1 ∧ p2) → (((True ∨ False) ∨ p4) ∧ ((p2 → (True ∧ False)) ∨ False))) ∨ p2) ∨ (p2 → (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205224975949818993856358732537 : ((((p3 ∨ True) ∧ False) ∨ (p4 → False)) ∨ (p4 → (((p3 ∧ (p5 ∨ (((False ∧ p4) → ((p3 → p2) → p2)) ∨ (p4 ∨ True)))) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199942257153786697450547801281 : (((p3 ∧ (p3 ∧ (p5 ∧ True))) ∨ (p4 ∨ p2)) → ((((((p3 ∧ (p2 ∧ p4)) → False) ∨ p3) ∨ ((p1 ∧ p2) ∧ p1)) ∨ True) ∨ (p1 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133868711751534707581518182541 : (((p3 ∧ ((p2 → ((p1 → (False → p5)) → ((((p5 ∨ False) ∨ ((p5 → p2) → p4)) → p2) → p5))) → p5)) ∧ False) ∨ (p1 → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179030654888123235946853092601 : (((p3 ∨ p5) → ((((False → p5) ∧ p5) ∨ (False ∧ (p5 ∧ p2))) ∨ p5)) ∨ ((p3 ∧ p1) → ((((p4 → False) ∨ p2) ∨ p1) ∨ (p4 ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147421179072400728438733980649 : (((((p5 → p2) → False) ∧ (p3 ∧ ((p5 ∨ p3) → (((False ∨ p5) ∧ ((p2 ∧ p5) ∨ p5)) ∧ p2)))) ∨ True) ∨ (False → ((p1 → p3) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147003125252018395779404215971 : ((((p4 → ((((p3 → p4) ∧ (p1 ∨ p5)) → False) ∨ ((False ∧ (p5 → p5)) ∧ p4))) ∧ (p3 ∧ p3)) ∧ p4) ∨ ((p3 ∨ True) ∨ (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149980106501579993125845021757 : ((p4 ∨ (((p3 ∧ p2) ∧ p2) ∨ ((p2 ∧ p4) ∧ (((True ∧ False) ∧ p4) ∧ (p5 ∨ (p1 ∧ (p5 ∨ p1))))))) ∨ ((False → True) ∧ (p1 → p1))) := by
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
theorem thm_5_vars_245423121386491295477111738335 : ((p2 ∧ p4) ∨ (((p5 → p3) → (((((True ∧ p2) ∨ (p2 ∧ False)) ∧ p3) → p5) ∨ (p2 ∨ p5))) ∨ (p5 → (True → (p1 → (False → p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306440673772556863621696849259 : (p1 ∨ ((False ∨ p5) ∨ ((p2 ∧ ((False → ((p4 → p3) → False)) → (p1 ∧ ((p3 ∨ (((p1 → True) → p1) ∨ p2)) ∧ True)))) ∨ (p3 → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249563108328390096636173626682 : ((p5 ∨ p2) ∨ (((False ∨ p1) ∧ p5) ∨ ((((p4 → p3) ∧ p2) → ((False ∧ p5) → (p1 ∨ p2))) → (p4 ∨ ((True ∨ (p2 ∧ True)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_119049850537570879775516686347 : ((p1 → (((((p1 ∨ p4) → True) ∨ p3) ∧ ((((p1 → p3) ∧ (True → (p2 ∨ p3))) ∧ (True ∨ True)) ∨ (p2 ∨ p2))) ∨ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50207045983302180456892460884 : (((((((True → ((p5 → p5) ∨ p1)) → (p1 ∧ (p3 → p2))) ∧ ((p2 ∨ p3) → p2)) → False) ∨ p3) ∨ ((p5 ∧ (p1 → p1)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616559443108405190530095523606 : ((((((p4 ∨ ((p4 ∧ p2) ∧ ((p4 ∧ False) ∨ p4))) ∨ p2) ∧ (((p1 → p3) ∧ p5) ∨ ((p3 ∨ (p1 ∧ (p5 ∧ p5))) ∧ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_204844741422043665655899980155 : (((((p4 ∧ p1) ∧ p5) → p5) → p3) ∨ (((p2 ∧ (p1 ∧ (((((p1 → False) → p5) → p5) ∧ (True → p4)) ∧ (True ∨ p5)))) → p5) ∨ p4)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : ((p1 → False) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h11
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616058633281054401517577321460 : (((((True ∨ (((((p3 → p4) → p1) ∧ ((True ∧ p4) → p4)) → p1) → p5)) → ((((p5 → (True → p2)) ∧ p2) ∨ p4) ∧ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257636720126205058946874572513 : ((p3 ∨ p2) → ((p5 ∨ (True ∧ (p2 → (p5 ∧ True)))) ∨ (((p2 ∨ p1) ∨ (p3 ∧ (p1 ∨ p3))) → (p3 ∨ (False → ((p3 ∨ p3) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h21
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338400048016523125767766450072 : (p1 → (((p5 ∨ (p2 ∧ p5)) ∨ p5) → (False ∨ ((((p2 → ((p2 ∨ p2) → (False ∧ p5))) ∧ ((p2 ∨ p5) → (p3 → p5))) → p3) ∨ p1)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119055047058557028091246548188 : ((p1 → ((((p3 ∨ (True ∨ (p3 ∧ (((((p5 ∨ p4) → p2) ∨ p5) ∨ p1) ∨ (False ∧ p1))))) ∧ (p4 → p3)) ∧ p5) → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40415321415934949927581131273 : ((((((((((p5 → (p3 ∧ p5)) ∨ p4) ∨ p5) → (p1 ∨ p4)) ∨ (True → True)) → False) → ((p3 ∨ True) ∨ (p5 → True))) ∨ p2) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247362033747053452763035445948 : ((False ∨ p1) ∨ ((((True ∨ (((p1 → False) ∨ p2) → False)) ∧ (((p2 → p4) → False) ∧ (p5 → (p3 → p2)))) ∨ True) ∨ (p1 → (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65300266901726409595110908070 : ((p3 ∨ (((p3 ∨ (((((False ∨ ((p3 ∧ p2) ∨ (p5 ∧ p1))) ∨ p5) → True) ∨ (p5 → True)) ∨ p3)) → (p1 ∧ False)) → (False ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187673546831655207629145436356 : ((True → ((False → p4) → ((True ∧ (False ∨ (True ∨ p5))) ∧ False))) → ((((p2 → p4) ∨ (p2 ∨ p2)) → (p1 ∧ (p5 ∨ p3))) → (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214327499179688240536553382187 : (((p1 ∨ (p5 ∧ p2)) → p4) ∨ ((p5 → (((p5 → (p1 ∨ (((p4 ∨ p4) → p3) ∧ p2))) ∨ (False → p4)) → p2)) ∨ ((p3 ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206018004908032112453296947207 : ((p2 ∧ ((p5 ∧ (True ∧ p1)) ∨ p4)) ∨ ((False ∨ True) ∨ ((p1 → (((True ∧ p1) ∧ p4) ∧ ((p5 → p4) ∧ p1))) ∧ ((True ∨ p5) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254993174191798208276186203155 : ((p4 ∧ p1) → ((((p4 ∧ (p4 ∨ False)) ∧ (((True ∨ (p2 → True)) → (p4 ∧ p5)) → ((p2 ∨ (p1 ∧ p5)) → p2))) ∨ (False → p1)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323278388787633890375862935282 : (p5 ∨ ((p3 → (((((True ∧ p5) ∧ (False ∧ p2)) → p1) ∨ (p3 ∧ (((p1 → p1) → p3) → (p2 → (True ∧ p2))))) → p1)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66475548729725195399123698664 : ((True → ((((p1 → (((((p4 ∨ p3) ∨ ((((p3 ∨ True) ∧ p3) → True) ∧ p3)) → (p4 ∨ False)) → p3) ∨ p1)) → p2) ∨ True) ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354070356830373736413325768724 : (p4 → (p4 → (p4 → ((((p4 ∧ p2) → p2) ∧ ((False ∨ ((((False ∨ p3) ∨ (p3 → False)) → False) ∨ (p3 ∨ (p2 ∧ p3)))) ∨ p4)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173064993787882013596749806679 : ((False ∨ ((p1 ∨ False) → (((p5 ∨ True) → True) → ((False ∧ (False → p1)) ∧ p4)))) ∨ ((p3 → True) ∨ ((p2 ∨ (False → p4)) ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116031344614013251190486942784 : (((p5 ∧ (True → (p5 → p2))) → ((p4 → p4) → ((p1 ∨ (p1 ∨ False)) → (((False → True) → (p1 → (p3 → p4))) ∨ p2)))) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54339358061303559845462316707 : (((p5 ∧ (False ∧ ((p3 ∨ True) → (False ∧ p5)))) ∧ (((((True ∧ p5) → (p1 → (p1 ∧ p5))) → p4) ∨ p4) → (True ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57853167120527664024466892430 : (((True ∨ (p5 ∨ p4)) → (p5 → ((True → (p3 ∨ p3)) ∨ ((p3 ∧ p5) ∨ (p5 ∨ (True ∧ (p4 ∧ (p1 ∨ (p2 ∧ (p4 ∨ p5)))))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249125898408455794904361165808 : ((p4 ∨ p2) ∨ (((True ∧ p4) ∨ ((((True ∧ False) ∨ (True → (p1 ∨ True))) ∨ (False → (p2 ∨ p2))) ∨ p1)) ∨ (p5 → ((p5 ∧ p2) ∧ True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803034378264401921138064526221 : (((p3 → (((p4 ∨ (p3 ∨ (p3 ∨ ((p4 ∧ p1) ∧ p4)))) → ((((p2 ∧ p4) → (p5 ∧ (p3 → (p3 → True)))) ∧ False) ∨ False)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784850022562423083680536495198 : (((p3 ∨ (p1 → (((((p3 ∨ (p3 → True)) → (p1 → p2)) ∧ (False ∨ (p2 ∨ p4))) ∨ (False ∧ (p2 ∧ p4))) ∧ ((p2 ∧ p5) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212862398462895370335707011696 : ((p2 → (p1 → (p5 ∨ p2))) ∧ (True → (p2 ∨ ((((p1 ∧ ((p5 → p1) → (p3 → p1))) → (False ∨ p2)) ∨ (p5 → p2)) ∨ (p3 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82902148724643342748823971115 : ((((((p1 → p4) ∧ ((((p5 ∨ p4) → p4) → p5) ∧ False)) ∨ ((p1 ∧ False) → (False → p5))) ∨ p1) → (False ∧ (True ∨ (True ∧ False)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → p4) ∧ ((((p5 ∨ p4) → p4) → p5) ∧ False)) ∨ ((p1 ∧ False) → (False → p5))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596167170700618624213952160924 : (((((((False ∧ p1) ∧ ((True ∧ True) ∧ p5)) ∨ False) ∧ ((((True ∧ (p1 → (p1 ∧ True))) ∨ p4) → False) ∧ (p2 ∨ (p4 → False)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33268951128944481356116056185 : ((p4 ∨ (((((p3 → p3) ∧ p4) → ((True → (p3 ∧ p5)) ∨ ((p3 ∧ (((False ∧ p3) ∨ p1) ∧ p5)) ∨ (p1 ∧ p5)))) → p4) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216124112316381478543701632075 : ((True → (p1 ∨ (p4 ∧ p3))) ∨ (((((((p5 ∨ p3) → (False ∧ p5)) ∨ p2) → p2) ∨ (p2 → (p1 → p3))) ∨ True) ∨ (p5 ∧ (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324504491141385899419204039911 : (p5 ∨ ((p3 ∧ ((False ∧ p5) ∧ p5)) ∨ (((True ∧ ((True ∨ ((False ∧ p2) ∨ p1)) ∧ p2)) ∨ ((False ∨ (p3 → (p1 ∧ p5))) ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48165898774807870789541633426 : ((((p1 ∨ p1) ∧ (p5 ∨ (True ∨ ((((p2 ∨ p2) ∨ p2) ∧ (p1 → p3)) ∨ (((p3 ∧ False) → (False ∧ p5)) ∨ p2))))) → (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213566843793179186660230789556 : ((((p1 ∨ p5) ∧ False) ∨ p1) ∨ ((((p2 ∧ False) → (False ∨ (p4 ∧ (p4 ∨ p4)))) → ((p1 ∧ p4) → (p3 ∨ (p3 → (p3 ∧ p4))))) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125532614526418298384400065300 : (((True → False) ∧ (((True → ((((p3 ∨ False) ∧ True) ∧ p1) ∧ (p3 → p2))) ∧ (p4 → ((True → p4) ∧ False))) ∨ (p3 ∧ True))) → (False ∨ p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741511226291976694868835867941 : ((((p5 ∨ p3) ∨ ((((p5 ∨ (True → (p2 ∨ p1))) → p1) ∨ True) → ((p5 ∨ False) → (p3 ∨ (((p1 ∨ p1) ∨ (p1 ∧ p4)) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159234434880162747347629322917 : ((p3 → (((p4 → ((p3 → (p3 ∨ p2)) ∨ ((False → p4) → ((p4 ∧ False) ∨ p1)))) ∨ p5) → p1)) ∨ (False ∨ (((True ∧ p3) → True) ∨ p1))) := by
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
theorem thm_5_vars_224309639828895683690731773276 : ((False → (False ∨ p2)) ∧ (((p3 ∨ (((p3 ∨ ((p1 ∧ (False ∧ False)) ∨ (((p5 ∧ p1) ∨ p2) → p4))) → p1) → True)) → (p4 ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_57430584016238584300632969812 : (((p3 ∨ (p5 ∧ p3)) ∨ ((p2 ∧ p5) ∨ ((p4 ∧ ((((p2 ∨ (p5 ∨ p1)) ∨ p4) ∨ ((True → True) ∨ p4)) ∧ (False ∨ p3))) → True))) ∨ p3) := by
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
theorem thm_5_vars_42403475362804258083962331800 : (((p4 ∧ (True → ((p2 → (((False → (True ∧ (((False → (p3 ∨ p1)) ∨ p1) ∨ p4))) → (p4 ∧ (p4 → p1))) → p1)) → p5))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587367581292034478575535632646 : ((((((p2 ∨ (((((p4 ∧ (p4 ∧ (False ∧ p1))) → True) ∧ (p5 ∨ (p3 → True))) ∧ (p4 ∨ (p2 ∨ p2))) → p4)) ∧ True) ∨ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47228685720352662371526578770 : ((((p5 ∨ (p2 ∧ (p1 ∨ ((p1 → p1) → p1)))) ∧ ((p5 ∧ (p1 → p2)) ∨ (p5 ∧ ((p1 → p4) ∧ (False ∧ False))))) ∨ (p4 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256783666767236261780404471785 : ((p1 ∨ p2) → ((False ∨ (p3 ∧ (p5 ∨ (((p4 ∨ p4) ∨ p2) ∧ p2)))) ∨ (((p1 → (p3 ∧ (p1 ∨ (p3 ∨ p2)))) ∨ (True ∨ False)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617437796956519477319831499329 : (((((p5 → ((p2 ∧ (p4 → p1)) ∨ (True ∧ True))) → (((p1 ∨ p5) ∨ (((p4 → (p1 → (p4 ∨ p1))) ∨ p2) ∨ p1)) → p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716673236122673445104761480509 : (((((p2 ∨ p2) → (True ∨ p5)) ∧ (((p4 → p3) → ((((p1 → False) ∨ p4) ∨ p3) ∨ p2)) ∨ (p2 → (((p5 ∨ p4) ∨ p3) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41015552988979323422998274714 : (((((p4 ∧ ((p4 ∧ ((False → (p3 ∧ (p2 ∨ True))) ∧ (p4 ∧ (False ∧ (False → (True → False)))))) → p1)) ∨ p4) → (p1 ∨ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208585972546722603291296931304 : (((p1 → p1) → (p4 ∧ (False ∧ False))) → ((p4 → p3) → ((((p5 ∨ ((p1 ∧ (p5 ∧ p5)) ∨ p3)) → (p3 ∧ (p3 ∨ p1))) → False) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186051868777501451595915611794 : ((((((p5 → True) ∨ ((p2 ∨ True) ∨ p4)) ∨ True) ∨ p1) ∨ False) → (((p5 ∨ p1) ∧ p4) ∨ (((True ∧ p1) ∧ p2) → ((True ∧ True) ∨ p2)))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h6
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h9 := h7.left
          let h10 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h14
              -- Conjunctions on the left can always be decomposed.
              let h15 := h14.left
              let h16 := h14.right
              -- Conjunctions on the left can always be decomposed.
              let h17 := h15.left
              let h18 := h15.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h16
            case inr h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h20
              -- Conjunctions on the left can always be decomposed.
              let h21 := h20.left
              let h22 := h20.right
              -- Conjunctions on the left can always be decomposed.
              let h23 := h21.left
              let h24 := h21.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h22
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
            -- Conjunctions on the left can always be decomposed.
            let h29 := h27.left
            let h30 := h27.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h32
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h34
    case inr h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h38
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h40
  case inr h43 =>
    -- False on the left can always be used.
    apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244322154690522620501204788878 : ((False ∧ False) ∨ (((True → (p5 ∧ (((p1 ∧ True) → p5) → (p1 ∨ p1)))) ∨ ((((p2 ∧ p3) → p2) ∧ p5) → (p5 ∧ True))) ∨ (p4 → False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177763636530421845742135884331 : ((((p4 ∨ p2) → (((p4 ∨ p3) → (p2 → (p1 ∨ p5))) ∨ True)) ∧ True) ∨ ((p5 → (p1 → (p2 ∨ (p1 ∧ (True ∧ (p3 ∨ False)))))) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_158411668999327146662273076828 : (((p1 ∧ p3) ∨ (((True → ((p2 → (False ∨ p1)) ∨ False)) → ((p2 → p3) ∨ (p5 ∨ p1))) → p1)) ∨ ((((True ∧ p1) → True) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148752355546907490254675625946 : (((p1 ∧ (True → ((p1 ∧ p4) ∧ False))) ∧ (((p2 → False) ∧ p2) ∧ ((p2 → p3) ∧ (p4 ∨ (False → p3))))) ∨ ((p5 ∨ p3) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52197815388389212324136362316 : ((((False → (p1 ∨ p5)) ∨ ((p4 ∨ (False ∨ p5)) → ((p5 ∧ p2) → (False → p1)))) → ((((False ∨ p3) ∨ False) ∨ p3) → (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187401456677482158509362215878 : ((p4 ∧ ((p2 → True) ∧ (((p1 ∨ (p1 ∧ p5)) ∨ p2) ∨ p4))) → (((False ∧ p3) ∨ p1) ∨ ((p4 ∨ p4) ∨ ((False ∧ (p2 ∧ p2)) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112246001522015910403641741610 : (((p3 ∨ ((p2 ∨ p5) ∧ ((p4 ∨ ((p3 ∨ p5) ∧ (p2 ∨ ((p1 ∧ p2) ∧ True)))) → ((p5 ∧ (p5 ∨ True)) ∨ False)))) ∨ True) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351735917873290188226168438221 : (p4 → (((p3 ∨ p5) ∧ ((p2 ∧ (p1 → (((p3 ∨ p2) → p5) → p5))) → p5)) ∨ (((p3 → (((p1 → p4) → p1) ∨ p3)) ∨ p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42642699657973006300075300102 : (((p3 ∨ (p5 → ((((((True ∨ p5) ∨ (p4 → False)) ∨ ((p2 ∨ False) → (p3 ∧ (p3 ∨ (True → p2))))) ∨ p5) ∧ p3) ∨ p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485475086300127977764690438613 : ((((((True ∧ (False → p4)) → p2) ∨ p2) ∨ ((((p1 → (p2 ∧ p5)) ∨ ((p5 → p4) → p1)) → p1) ∨ (p5 → ((p1 ∧ p4) ∨ True)))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246575537170358707525947114555 : ((p5 ∧ p2) ∨ ((((p4 ∧ (p5 → ((True → p3) ∨ (p5 ∧ (True ∨ ((p3 ∧ True) → p2)))))) ∧ p4) ∨ p4) → ((p1 ∨ (p3 ∧ p1)) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627192205957832483097519091394 : (((((((((True ∨ (p5 ∨ (False → p5))) → (True ∨ True)) ∨ (p1 ∧ ((True → True) → p4))) ∧ (p1 ∧ (True ∨ p5))) ∨ p5) ∧ True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742608361575240019542742163930 : ((((p2 → p3) ∨ ((p2 ∨ (((False ∧ p3) ∨ (p2 ∨ True)) ∨ ((p3 ∨ p4) ∨ (p4 → (p4 ∨ (p3 ∨ True)))))) → ((p1 → p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



