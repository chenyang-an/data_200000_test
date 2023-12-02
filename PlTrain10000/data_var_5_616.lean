variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736343682548538890426462535492 : ((((False → p5) ∧ (((p3 → (p4 ∧ p1)) → (p2 ∨ (((p2 ∨ p5) ∨ (p3 ∧ p4)) ∧ ((p5 ∧ (p1 ∨ (p4 ∨ False))) → p2)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177798614505307876359634531736 : (((p2 ∨ (p3 ∧ ((p4 ∧ p5) ∨ (p3 ∨ (p1 ∧ (p3 ∧ p3)))))) ∧ p1) ∨ ((p2 ∧ p2) ∨ ((False → ((p1 → p2) ∧ True)) → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37100866198481066799815806578 : ((((((((True ∨ p3) → ((((p3 → (p4 ∨ p3)) → p2) ∧ False) → True)) → (p2 → ((True ∨ p4) ∨ p5))) ∨ p2) → p3) ∧ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314261470181637070783490181107 : (p3 ∨ (((p1 ∧ (p1 ∨ True)) ∨ ((p4 → p1) → (p1 → (((p4 ∨ p5) ∨ (p4 → p5)) ∨ ((True ∨ p4) ∧ True))))) ∨ ((p4 ∧ p5) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_67479180144028901791256444130 : ((p1 → (((p4 ∨ ((((p5 ∨ False) ∨ p5) ∨ p2) ∨ ((False → p3) → True))) ∧ False) ∨ (p3 → ((p4 ∧ p2) → (p3 → (p1 ∨ False)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38873721394500262030282688754 : ((((p3 → (False ∨ p2)) ∧ ((p1 → ((p2 → ((p2 ∨ p3) → (p3 ∨ p4))) ∨ ((False ∧ (p3 → p4)) ∧ (True → p3)))) ∨ p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111569583506995971704112589897 : ((((((p1 ∧ p3) → p2) ∨ ((p3 ∨ ((False → p4) ∧ (p1 → (p1 ∧ p4)))) → (((False ∧ p2) ∧ False) ∨ p1))) ∧ p2) ∨ True) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136353327640226504941947821213 : (((p3 → ((True → True) → p1)) ∧ (p5 ∨ (p4 ∧ (p2 ∨ ((True → (p3 ∨ p5)) ∧ (False ∨ (p1 ∨ (p1 ∧ p2)))))))) ∨ ((True ∨ p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178245891471100588650234503424 : ((((((p4 ∨ (p2 ∧ p2)) ∧ (True → False)) ∧ p1) ∨ True) ∧ (p3 → p3)) ∨ ((p1 ∧ False) → (((p2 → False) → p1) ∧ (p1 → (p5 ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174496175317729260424241834817 : (((((True ∨ True) ∧ (False → p2)) ∨ p3) ∨ ((p1 → p5) ∨ (p1 ∨ (p1 → True)))) → ((p4 ∧ p1) ∨ (False → ((p4 ∧ (False → p2)) ∧ p4)))) := by
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
        -- False on the left can always be used.
        apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h18
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
        -- False on the left can always be used.
        apply False.elim h21
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4120224572514634644641079975 : (p3 ∨ ((False ∨ p3) → ((False ∨ ((((True ∨ True) → ((p3 ∨ ((p5 ∧ (p4 ∨ p3)) → (p1 → True))) → p5)) ∧ p5) ∧ False)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50836387431551201235450937459 : ((((((True → (p4 ∨ p3)) ∨ p5) ∨ ((p3 ∨ (True → (True → (False → False)))) ∧ p4)) ∧ p3) ∧ (((p4 ∧ True) ∨ (p3 ∨ p4)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163036108253004058514135435273 : (((True ∧ ((p4 → (p5 ∨ p1)) ∧ (p4 ∧ ((p4 ∧ p2) ∧ p5)))) ∨ (p3 → (False ∨ p3))) ∧ (p2 ∨ ((True ∨ (p1 ∧ False)) ∧ (p4 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215825139724681414655615125049 : ((p2 ∨ ((p3 ∧ True) ∨ p5)) ∨ (p1 → (((False → (p2 ∧ (True ∨ (p4 ∨ p2)))) → (True ∧ ((False ∧ p4) ∧ p1))) ∨ ((p3 → p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146953863958182222298275587486 : (((((True → p2) → ((p5 ∨ ((p2 ∨ p1) → (p2 ∧ ((p3 ∧ p2) ∧ p3)))) ∨ (True ∨ p5))) ∨ p3) ∧ p2) ∨ (True ∧ ((True ∧ False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637770128827840693438072327897 : (((((p5 ∧ (p2 ∨ ((True → ((p1 ∨ p3) ∧ p1)) ∨ p2))) → (((False → (p3 ∨ (True → p3))) ∨ True) ∨ ((True ∧ p4) ∨ p2))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89118475727161520338432009302 : ((((p3 → p3) ∨ p2) ∧ (((p4 → p3) ∧ ((True ∨ (p1 ∧ p3)) → (False ∧ p2))) ∧ ((True ∨ p4) → ((False ∨ (p5 → p1)) → p4)))) → p4) := by
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
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (p1 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (True ∨ (p1 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118766054331978947135945731220 : ((p5 ∨ (False ∧ ((True → p3) ∧ ((False → (p3 ∧ ((p2 ∨ p5) ∧ p2))) → (((p3 ∨ ((True ∨ True) → p3)) ∧ True) → p5))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337734357569282806323656244759 : (p1 → ((((((((False ∧ True) ∨ p4) ∨ False) ∧ False) ∨ p5) → p3) → (p5 → (p2 ∨ p3))) ∧ (((p4 ∨ ((p5 ∨ False) ∨ p4)) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((False ∧ True) ∨ p4) ∨ False) ∧ False) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54936120811771929425820614147 : ((((p1 → ((p2 → p5) ∨ p3)) → p2) ∧ (p4 → (((p1 ∨ (p5 ∨ p3)) ∨ p1) ∨ (p4 ∨ (((p1 ∨ p1) → (False ∨ p5)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65757193531952406309906260936 : ((p4 ∨ ((((True → p2) ∨ ((False → (((p1 → p1) → (p1 → p1)) ∨ False)) ∨ p1)) → (p5 ∨ p2)) ∨ (p4 ∨ (p2 ∧ (False ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167886686580625942359022852297 : (((p5 ∨ ((p2 ∨ ((p4 → True) ∧ p2)) → (True ∨ p5))) → (((p1 ∧ p3) → p3) → False)) → (((False → p3) ∧ p3) ∧ (p1 ∧ (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ ((p2 ∨ ((p4 → True) ∧ p2)) → (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p1 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h10
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (p5 ∨ ((p2 ∨ ((p4 → True) ∧ p2)) → (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h15
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h22 : ((p1 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h25
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h26 := h21 h22
  -- False on the left can always be used.
  apply False.elim h26
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h27 : (p5 ∨ ((p2 ∨ ((p4 → True) ∧ p2)) → (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h33 := h1 h27
  -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
  have h34 : ((p1 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h35
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h37
  -- We have shown the premise of h33, we can now drive its conclusion.
  let h38 := h33 h34
  -- False on the left can always be used.
  apply False.elim h38
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h39 : (p5 ∨ ((p2 ∨ ((p4 → True) ∧ p2)) → (True ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h40
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h45 := h1 h39
  -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
  have h46 : ((p1 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h47
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- One of the premise coincides with the conclusion.
    exact h49
  -- We have shown the premise of h45, we can now drive its conclusion.
  let h50 := h45 h46
  -- False on the left can always be used.
  apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197114105130324797551816639449 : (((False ∨ (p4 ∨ (p4 ∨ (False ∨ p3)))) ∨ True) ∨ (p5 → ((p1 ∧ (((p3 ∧ p4) ∧ ((True ∧ (p3 ∨ p2)) ∨ p1)) ∨ False)) ∨ (p2 → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314744200842362673723834619532 : (p3 ∨ ((((p2 ∧ p1) ∨ (p4 → (False → ((p1 ∧ p5) ∧ p3)))) → (p4 ∧ p5)) ∨ (p4 → (True ∧ (((False ∧ p5) → True) → (p4 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_61263272851682188640004598163 : ((False ∧ (p1 ∨ ((((p5 ∧ (((p1 → ((p3 ∧ p3) ∧ p4)) ∧ (p1 ∧ False)) ∧ p4)) ∧ (((False ∧ p4) ∧ p2) → p4)) ∧ p4) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55257122431595568821487093801 : ((((p3 ∨ p1) ∨ (p3 ∧ (True ∨ False))) ∨ ((False ∧ (False ∧ ((p3 → p4) ∨ False))) ∨ (False → (((False → (p4 ∧ p2)) ∧ p5) ∧ p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114975368036389122653381137665 : ((((p4 ∧ (((p5 ∨ p2) → (p2 ∧ (p3 → p4))) ∨ p1)) ∧ p3) ∧ (((((p1 ∧ (p1 ∧ True)) → p5) ∨ False) ∧ p1) → p3)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632024787504450939320722590135 : ((((((True ∧ (p1 ∨ True)) → (False ∧ ((((p5 ∧ (p3 → ((p3 → (p4 → (p2 → p5))) → p5))) ∨ p4) ∧ False) ∧ p1))) → p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165712844437563619053811966126 : ((((False ∧ p2) ∧ (p2 ∨ p3)) ∧ ((False ∨ p4) → ((True ∧ (True → (p5 ∧ p2))) ∧ True))) ∨ ((True ∨ (p1 → p2)) → (p3 ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205837598531230805366585116480 : (((p1 → False) → ((True → p1) ∨ p5)) ∨ (((p5 ∨ ((True ∨ p2) ∨ p1)) → (p3 → False)) → (True ∧ (p3 → ((p5 ∧ (p4 ∨ p1)) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p5 ∨ ((True ∨ p2) ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (p5 ∨ ((True ∨ p2) ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54137336227582282072098039759 : (((p4 ∨ (True ∧ ((False ∧ (p1 ∨ p5)) → (p1 ∧ p1)))) → (p3 ∧ (p4 → ((((p1 → p4) ∧ p1) ∨ p1) ∧ (False ∧ (p4 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768118299244349686122887887112 : (((p5 ∧ ((((((p1 → False) ∨ (True ∧ p1)) ∨ (p4 ∨ p3)) ∨ p1) ∧ ((p1 ∧ (((p5 ∨ p1) ∧ p3) ∧ p1)) ∧ p2)) ∨ (p1 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255794942328658975154008575740 : ((True ∨ False) → ((((p2 ∨ (p2 ∨ (p2 ∧ (True ∨ (p3 ∨ p1))))) → p2) → (((p3 ∨ (((p1 → p5) → p4) ∨ p3)) ∨ p5) ∧ False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p2 ∨ (p2 ∨ (p2 ∧ (True ∨ (p3 ∨ p1))))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- One of the premise coincides with the conclusion.
              exact h10
            case inr h15 =>
              -- One of the premise coincides with the conclusion.
              exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h4
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61344924855477765667511834061 : ((p1 ∧ (((p4 → (False → ((False ∧ (False ∧ (p2 ∨ (True ∧ ((p3 ∨ p5) ∨ p2))))) → (p2 ∨ p5)))) ∧ ((p2 ∧ p4) ∧ p4)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738746840195632928342282976299 : ((((p2 ∧ p3) ∨ ((True ∧ ((((((p4 ∨ p2) ∨ p1) → p1) → p3) → ((p4 ∨ p2) ∨ p4)) ∨ (p3 → (p2 → p5)))) ∧ (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244188099701416945044427174725 : ((True ∧ p5) ∨ (((p5 ∨ ((((False ∨ p2) ∨ p2) ∨ p5) ∧ (p2 ∧ (((p3 → p1) ∨ p2) ∧ (p3 ∧ (False → (p4 ∧ p2))))))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625888392292826774384593882030 : ((((p2 → ((p1 ∧ ((p3 ∨ (p5 ∧ (((p1 ∧ (p5 ∨ p4)) ∧ True) ∨ p5))) → ((True → (p4 ∧ False)) ∨ (p3 → False)))) ∨ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_190936406806575839815845746706 : ((((False ∧ p3) ∧ (False ∧ p4)) ∧ ((p1 → True) ∧ p1)) ∨ ((((p1 ∨ (False ∨ p5)) ∨ p1) → False) ∨ ((((True → False) → True) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714344328184471469532030174093 : (((((True ∨ (p1 ∧ p3)) ∨ (False ∧ p3)) → ((p3 ∧ (((p5 → False) ∨ p2) → ((p4 ∧ p5) ∧ p3))) → (p3 ∧ ((p5 ∨ p3) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52060296471285007918649842219 : (((p5 → (((True ∨ True) ∧ (p1 ∧ (p3 → (p3 → p1)))) ∨ (p2 ∧ (p4 ∨ p4)))) ∨ (((p4 ∧ False) ∨ False) → (False → (p3 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62845870618223367940111804636 : ((p4 ∧ (((p5 ∧ p2) ∨ ((p5 → p1) → True)) → (False ∨ ((((((p5 ∨ p3) ∨ (p2 ∧ p2)) ∧ p5) ∧ p4) ∨ p5) → (p1 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54768080776446573354406214949 : ((((p2 → False) → (((False ∨ False) → p2) ∨ p3)) → (((((False → ((False ∨ False) → (p5 → p1))) → (p3 ∨ p2)) → p2) ∧ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803353361406222998709145150490 : (((p3 → (((p5 → False) ∨ ((p2 ∨ (((p2 → p2) ∨ p2) → ((p1 ∨ False) ∨ p4))) ∧ (True ∨ (p3 ∧ ((p1 → p5) → False))))) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_300376412885913566284714730066 : (False ∨ ((((p1 ∧ p4) ∨ ((p2 ∧ ((True ∧ (p5 → (True ∧ (p2 ∧ False)))) → True)) ∧ True)) ∧ ((p4 ∨ p2) ∨ p2)) ∨ ((p3 → p3) ∨ p2))) := by
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
theorem thm_5_vars_45517049502386028093267226045 : (((p1 ∨ (((p5 → p3) ∨ (True ∧ ((p2 ∨ (p5 ∧ (p5 ∧ ((p1 ∧ True) ∧ p4)))) ∨ p4))) ∧ (False ∨ (False → (p5 → p5))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606982155106473468207840839521 : ((((((((p5 ∨ p4) → (((p2 ∨ p2) ∧ (True ∨ p4)) ∨ p4)) → (p1 ∧ p5)) ∨ (((True ∧ (False ∨ p2)) → False) ∨ p1)) ∧ False) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_41623114190370029093219701954 : (((((((p3 ∨ True) → p2) ∨ (True ∨ p5)) → False) → (True → ((p4 ∧ ((p3 → p2) → (((p2 ∨ p4) → p2) ∧ p2))) ∨ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710805457923368245924736158475 : (((((False ∧ p5) ∧ (True ∧ (p2 ∧ p3))) ∧ ((((p2 → (True → p5)) ∨ p1) → (True ∧ (False ∧ p5))) ∧ (((p2 ∧ p4) ∨ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64673721303346689572423300461 : ((p1 ∨ (p2 ∨ (p5 ∧ ((((((True ∧ p5) ∧ ((p5 → p3) → False)) ∨ p5) ∧ p4) → ((p1 ∨ (True → p4)) ∨ (p2 ∨ p4))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793632164942777086959582519179 : (((True → (p4 ∨ ((False ∨ p4) ∨ (((((p4 ∧ p3) ∧ p1) ∧ p1) ∨ p3) → (((p2 ∧ (p1 → p2)) ∧ p1) → ((p5 ∨ True) ∨ True)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193181344177447309921914935382 : (((((p5 ∨ False) ∨ False) → False) → ((p4 → False) ∧ False)) → ((True ∧ ((((p4 ∨ True) ∨ (p5 → p2)) → p2) ∨ (p1 ∨ p3))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88240436132835217044916667805 : (((False ∨ ((p4 ∨ True) → False)) ∧ ((((True ∧ p5) ∨ ((p2 → p1) ∧ p1)) → p5) ∧ (((p4 ∧ (True ∨ False)) → (p4 ∨ True)) ∧ p2))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708407121722906917338378741418 : (((((True ∧ (False ∨ ((False ∧ p2) ∨ p2))) ∧ p4) → ((True → p5) → ((p3 ∧ ((((p1 → False) → p1) ∨ p4) ∨ False)) ∨ (p1 ∨ p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76305096835631883616096712930 : ((((((p2 → p4) → ((p3 ∨ False) ∧ p2)) → (True → ((p2 ∧ ((p1 ∨ ((False ∧ p5) → p5)) ∨ True)) ∨ p1))) ∨ (False → p1)) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 → p4) → ((p3 ∨ False) ∧ p2)) → (True → ((p2 ∧ ((p1 ∨ ((False ∧ p5) → p5)) ∨ True)) ∨ p1))) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346591011491356094060864951071 : (p3 → ((((p4 → (((p5 ∧ (True ∧ (True ∧ p2))) ∧ (p2 → (p2 ∨ p2))) ∧ p3)) → ((p2 ∧ p3) ∧ False)) ∨ p1) ∨ (p2 ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226260887776441570240117950925 : (((p3 ∨ p4) ∨ p2) ∨ (((p1 ∨ True) → (p4 ∨ ((((p2 → ((p1 ∨ (p1 ∧ p5)) ∨ p2)) ∧ p2) ∧ ((p4 ∨ p2) → False)) ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_656782049065772617704369764762 : (((((((p5 → (p2 ∨ p5)) → p4) → p3) → (((True ∧ (False → p5)) → p5) ∧ (p4 → ((p3 ∨ (p4 → p4)) ∨ False)))) ∨ (True ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198597155065795641538189231081 : ((p2 ∨ ((p3 → ((p2 ∧ p5) ∧ False)) ∨ p4)) ∨ (((p2 ∨ (p1 ∧ ((p5 → p3) ∧ False))) ∧ p4) ∨ (((p1 → p1) ∧ (p2 ∧ p5)) → p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67959011504893450783534562164 : ((p2 → ((((p2 → p5) ∨ p2) → True) → ((((p1 ∨ p4) ∨ p3) → p5) → (True → (((False → ((False ∨ p5) ∨ p1)) → p1) → p1))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → ((False ∨ p5) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68260831505413800349045748862 : ((p3 → ((p4 → (((p3 ∨ p4) → p3) → ((((p1 ∨ (p5 ∨ p5)) ∧ p4) ∧ ((p4 ∧ False) ∧ True)) ∨ (p3 → p5)))) ∧ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727845713440173348319831218043 : ((((p1 ∨ (p4 ∨ p4)) ∨ ((((p5 → (False ∨ (p3 → p2))) → p3) ∧ ((p2 → (p4 ∨ p4)) → True)) ∨ (True ∨ (False ∧ (False ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52312039396791341010915833160 : (((((p5 ∧ (p5 ∨ (((False ∧ (p2 → False)) ∨ p4) → p3))) ∧ p3) ∨ True) ∧ (((True ∨ False) ∨ ((p1 ∨ (p2 ∨ p5)) → True)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_858816142475648298913560116857 : (((((p2 ∧ ((False ∨ p2) → (((p3 → (((True ∨ p4) → p2) → p1)) ∧ (False → (True ∨ ((p4 ∧ p3) → p5)))) ∧ False))) → p5) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((False ∨ p2) → (((p3 → (((True ∨ p4) → p2) → p1)) ∧ (False → (True ∨ ((p4 ∧ p3) → p5)))) ∧ False))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (False ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345527436664215847832113215756 : (p3 → ((((p1 → ((p1 ∨ True) ∧ ((False → p1) ∧ p2))) ∧ p4) ∨ ((p1 ∧ (p2 → (p1 ∧ ((False ∧ (False → p1)) ∨ p4)))) ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62280470480986774011770350128 : ((p3 ∧ (((True ∧ ((p4 → (p5 → p4)) → p4)) ∧ (((((p1 ∨ (p3 → p5)) ∧ p4) → (p2 ∨ p1)) → (p3 ∧ p5)) ∧ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228679634987773592336697089211 : ((p2 ∨ (False ∨ p3)) ∨ ((False ∧ ((p1 ∧ (False ∨ p4)) ∨ (((True → (p4 → False)) ∧ p4) ∨ ((((True → p2) → False) ∨ False) ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340845105109204534632787118918 : (p2 → (((p3 ∨ ((False ∧ (((p4 ∨ (p3 ∨ (True ∨ p4))) ∧ False) ∨ (p4 → p4))) ∨ ((True ∨ p4) ∨ p2))) ∧ ((False → True) ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314273712385749477861997757814 : (p3 ∨ ((p5 ∧ ((True → ((((p3 ∨ True) ∨ True) ∧ p3) → (p4 ∧ ((True → (p5 ∨ False)) → (p5 ∧ False))))) ∧ p2)) ∨ (False ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_206778383445533677781467639825 : ((p4 → ((False ∨ p3) ∨ (False ∨ p2))) ∨ (((p4 → (((p1 ∨ p3) → (p5 ∧ p2)) → ((False ∧ p5) ∨ p4))) → p5) ∨ (p2 → (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249459215675757207389612515800 : ((p5 ∨ False) ∨ (p5 ∨ (p1 ∨ (((((p2 → p4) ∧ (p3 ∨ p2)) ∨ p5) → (p5 ∨ False)) ∨ ((p3 ∨ ((p4 → False) ∨ True)) ∧ (False → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699592566076719540678787792115 : ((((((((True ∧ p5) → ((True → p5) ∨ p1)) ∧ p4) → False) → p5) → ((True → p1) ∨ (((((p2 ∧ False) ∨ False) → p1) → p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658766752328282557728192827298 : ((((p5 ∨ ((((((p1 ∧ p2) → (p5 ∨ (p2 ∧ p5))) → True) ∨ True) ∧ p1) → (p4 ∧ (p3 → ((p2 ∨ p4) ∧ p2))))) ∨ (p2 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_62687663867195948078168413652 : ((p4 ∧ (((False → (True ∧ (((((p1 ∨ (p1 → (p5 ∧ p2))) ∨ True) ∧ ((p3 ∨ (p5 ∨ p5)) → True)) → True) ∧ p2))) ∧ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701264588284151127694995519787 : (((((p5 ∨ ((False ∧ (p4 ∨ p5)) ∨ p5)) ∨ (True → p1)) ∧ (((True ∨ True) ∨ False) → ((False ∧ ((p4 → p4) ∧ p3)) ∧ (p4 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317996827257144126751379276690 : (p4 ∨ ((p5 → ((p4 → p3) → ((p3 → p4) ∧ ((p3 ∧ (p3 ∨ ((p5 ∨ (p4 ∨ (True ∧ p1))) → p1))) → (False ∧ (p3 → False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117533329466215747978165480012 : ((p2 ∧ ((p3 ∨ ((p4 ∧ ((p1 ∨ ((p5 ∧ ((True ∧ p5) → True)) ∧ p1)) ∨ ((p5 → False) → False))) ∧ p1)) ∧ (p4 ∧ False))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637932310131295806189894915479 : (((((p2 ∨ (True ∨ (True ∧ ((p5 ∧ p1) → p3)))) ∧ (p3 ∧ ((((p5 → (True → p3)) → p1) ∧ (False → (True ∧ p1))) ∧ p4))) → p1) ∨ False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → (True → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h11
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h23 : (p5 → (True → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h26 := h21 h23
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h3.left
      let h31 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h36 : (p5 → (True → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h37
        -- Implications on the right can always be decomposed.
        intro h38
        -- One of the premise coincides with the conclusion.
        exact h30
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h39 := h34 h36
      -- One of the premise coincides with the conclusion.
      exact h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213183845599791256749236151586 : ((((p2 ∨ p3) ∨ p1) ∧ p5) ∨ ((p2 → p4) ∨ (((True → ((((p5 ∨ p1) → (p5 ∧ (p2 ∧ p3))) ∧ False) ∧ p1)) ∨ p2) ∨ (False → True)))) := by
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
theorem thm_5_vars_115179739480077311440524847829 : (((((p2 ∨ (p5 ∧ (p1 → p2))) ∧ p5) ∧ (False ∧ p5)) ∧ ((((False ∧ p1) → ((p4 → p3) ∨ p3)) → p2) → (p5 → p3))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319775514807672740044219704761 : (p4 ∨ (((((p2 → p5) → False) ∨ p3) → p4) → (((p1 ∧ (p5 → (p3 ∨ p2))) ∨ (True ∨ p4)) ∨ (((p5 ∨ p1) ∨ (p3 ∨ p1)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254329045627918823101698264344 : ((p2 ∧ p4) → ((((False ∧ ((((False ∨ p5) ∨ (p1 → ((p2 → False) ∨ (p4 → (p5 ∧ p1))))) ∧ p4) ∧ (False ∧ p1))) ∨ p5) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_207784584670435772785122292989 : (((p5 ∨ (p1 ∨ (p5 ∨ True))) → False) → ((p2 → (p3 ∨ ((p2 → (p5 ∨ ((p4 → p4) → False))) ∨ (p2 ∧ (False ∧ p4))))) ∧ (True ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ (p1 ∨ (p5 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ (p1 ∨ (p5 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207751521033078616270138638584 : (((False ∨ ((p3 ∨ True) → p3)) → p4) → (((p4 ∧ (False ∨ p4)) ∨ True) ∨ ((((p3 → p3) ∧ (False → p4)) ∧ (True ∨ p5)) ∧ (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178942265603439110674427783694 : (((p2 ∧ p1) ∨ (p2 → ((p2 ∧ (((p5 ∨ p4) ∧ p1) ∨ p2)) ∨ True))) ∨ ((p3 → (((p1 ∧ p5) → p2) ∨ p4)) → ((p3 → p1) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355636537011457312868254682909 : (p5 → ((p1 → ((((p5 ∨ (p4 ∧ p4)) → ((((p4 ∧ ((False ∧ True) ∨ True)) ∨ False) ∧ p3) ∨ False)) ∧ (p4 → p5)) → p4)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22607020723662351108639131786 : (((((p2 ∧ p4) → p3) → (False → p5)) ∧ (((((True → p5) ∧ p2) ∨ ((p2 ∧ (p4 ∧ False)) → p3)) ∧ (p5 → False)) → (p5 → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655486536246374327422490523128 : (((((p5 → (((p5 ∨ p3) ∧ True) → (((p4 → (p3 ∧ (p5 → (True ∧ (False ∨ p4))))) ∧ p5) ∨ False))) ∨ (p4 ∨ p2)) ∨ (p4 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113370945384745119780988535636 : (((p1 ∨ (((p4 ∧ p4) → ((p2 ∨ p3) ∨ (((p1 ∧ (p3 ∧ p4)) → p1) → p1))) ∨ (True → (p3 → True)))) ∧ (p2 → p2)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8134371315056147260452470355 : ((((True ∧ ((((p3 ∨ (((p3 ∨ (p2 ∧ ((p3 ∧ p1) ∨ p1))) ∨ (p5 ∨ p5)) ∨ p5)) ∧ p3) ∨ (p3 ∨ p2)) ∧ True)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_161527045676107704340945431612 : ((p5 ∧ (((p2 ∧ ((p4 ∨ (False → p5)) ∧ False)) → (((True ∨ p1) ∨ True) → (p4 → p3))) ∧ p1)) → (((p4 ∧ p1) → False) ∨ (p3 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152550151167703896195345549086 : ((((True ∨ p5) → False) → (p4 ∨ ((p1 ∨ ((False ∨ ((p2 → p2) → (True → p5))) → True)) ∧ (p2 ∧ True)))) → ((p4 ∧ (p5 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258520024304428900581677742899 : ((p5 ∨ p3) → ((((((p4 ∧ True) → ((False → ((p2 → ((p1 ∨ p2) → True)) ∨ p3)) → p3)) ∧ p5) ∧ ((p3 ∨ p5) ∧ p5)) ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_218966561527450865968363542403 : ((p4 ∧ ((p3 ∧ p4) ∨ p3)) → (((False → (p5 → p1)) ∧ ((p3 ∧ (True ∧ (p5 ∨ False))) ∨ (False ∧ (False → p2)))) ∨ (p3 ∧ (p3 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196743821450488406209131764118 : (((((p5 ∨ False) → p1) ∧ (p3 ∧ p1)) ∧ p3) ∨ (((((True ∧ (p3 → p3)) ∧ False) ∧ p2) ∨ p2) → (False ∨ (p4 ∨ (p3 ∨ (True → True)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319303838685817704055273861213 : (p4 ∨ (((p3 → (p4 ∧ (((p5 ∧ p5) → p5) → (p2 ∧ (p1 ∨ p4))))) ∧ (p1 ∨ p3)) → ((True ∧ (False ∨ (p1 ∨ (p5 ∨ True)))) ∨ p1))) := by
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
theorem thm_5_vars_631307197256572501623045728165 : ((((((p5 ∧ ((((p3 ∨ p1) → ((p1 → True) → (((p4 ∨ True) ∧ p3) ∨ (p5 ∧ p3)))) ∧ (p5 → True)) → p2)) → p1) → False) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715148815649357656117664570730 : ((((p5 ∨ (p4 ∧ ((p4 ∨ False) → p4))) → ((((p5 ∧ (p4 → (((p5 → False) ∧ (p1 → False)) ∨ (True ∧ p3)))) ∨ True) ∨ p4) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51962444389314697246038532787 : ((((p5 ∨ ((False ∧ p5) → True)) → (((p5 ∧ p1) ∧ p4) ∨ (p1 ∧ (p4 → p2)))) ∨ (False → (p3 ∨ ((False ∨ (p4 ∧ True)) ∧ p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112856624316656826479429796176 : (((((p5 ∧ p5) ∨ False) ∨ (((((p1 ∧ ((p5 ∧ p4) ∧ (False ∨ p2))) ∨ p3) → (False ∨ (False ∧ p1))) → p4) ∧ p2)) → p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63331173081836809966999024430 : ((p5 ∧ ((False ∨ p3) → ((p5 ∨ ((p1 → ((p2 ∨ p2) ∨ p2)) → p1)) ∧ (p3 ∨ ((p1 ∧ ((p3 ∨ p2) ∨ p3)) ∨ (p1 ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



