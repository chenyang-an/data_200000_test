variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200968016631548338054751698832 : ((p2 ∨ (False ∧ (((True ∨ p3) → False) ∨ p3))) → ((p1 → p3) → (((p1 → (True ∨ (((p5 ∧ p2) ∨ p4) ∧ True))) → False) → (p2 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → (True ∨ (((p5 ∧ p2) ∨ p4) ∧ True))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150559385380479125869488641680 : ((((((p5 ∨ p2) ∨ p2) ∧ p5) → ((((p3 ∨ True) ∨ p3) ∨ (((False ∨ p4) → p2) ∧ p1)) ∧ False)) ∧ p5) → (((p1 ∨ p2) → p3) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p5 ∨ p2) ∨ p2) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135369945348191605982646066916 : ((((((False ∧ p5) ∨ False) ∧ (p2 → ((((p4 → p5) ∧ p2) ∧ (p4 → p1)) ∨ p5))) ∧ p4) ∨ (p5 → (p3 → p4))) ∨ ((p4 ∧ p1) → p4)) := by
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
theorem thm_5_vars_121533269451576160921740955554 : (((((p4 ∧ ((p5 ∨ (True ∧ p2)) ∧ (((p2 ∧ (p1 → ((True ∧ p4) ∧ p1))) ∧ p4) ∧ True))) ∨ p1) ∨ (p2 → True)) → p1) → (p1 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ ((p5 ∨ (True ∧ p2)) ∧ (((p2 ∧ (p1 → ((True ∧ p4) ∧ p1))) ∧ p4) ∧ True))) ∨ p1) ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54349760973053977567235144199 : (((p1 ∨ ((p1 ∧ p4) ∨ (False ∨ (p5 → p2)))) ∧ (p4 → (((p2 ∧ p5) → ((p2 → (p1 ∧ (False → (False ∧ False)))) ∧ p4)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693897516168835519712061026829 : (((((p4 → (p5 ∧ (p1 → (((p5 → p3) → (True ∧ False)) ∧ p4)))) → p2) ∨ (((p5 ∨ p4) ∧ p3) ∧ ((p3 ∨ (p3 ∧ False)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136664536919202118068063861634 : (((True ∨ (p4 ∨ False)) → (p5 ∧ (p2 → (True ∧ ((p3 ∨ p5) ∧ (p3 ∨ (p4 → ((p3 ∧ (p2 ∨ True)) ∧ p2)))))))) ∨ ((p4 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46920545235269585446034892561 : (((((p5 ∨ ((p5 ∨ False) ∨ p2)) ∧ ((p4 → (p3 → p5)) → ((p3 ∧ p1) ∧ (((True ∨ p1) ∧ True) ∨ p5)))) ∨ True) ∨ (True ∧ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184774548860675925676622160157 : ((((True ∧ (p5 ∧ p5)) ∧ p1) ∨ (p3 ∨ ((False → p3) → p2))) ∨ ((p1 ∨ p4) ∨ (True → (p3 ∨ (False → (p3 ∧ (p4 ∧ (True ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135406358247184051954071660828 : (((((False → p5) ∨ (p3 ∨ True)) ∧ (True → ((False → (False ∧ p3)) → (False ∨ (p3 ∨ p3))))) ∨ ((p3 → p1) ∨ True)) ∨ (p5 → (p4 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41586526914728357298093423007 : (((((p5 → p5) ∨ (p4 ∨ ((p1 ∧ p2) ∧ p3))) ∧ (p4 ∨ (((False → p5) ∧ ((False ∨ False) ∧ (False → p1))) ∨ (p1 ∨ p4)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172677345831710386867482768440 : (((p5 → p3) ∧ (((p3 → p5) → ((False ∨ p4) ∨ (p4 → p2))) → (p4 ∧ p2))) ∨ ((p3 ∨ p3) → (p5 → ((False ∨ p5) ∨ (p4 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350970600530665027781923957304 : (p4 → (((p2 → ((p1 ∨ True) ∧ True)) ∧ ((((((True ∨ p3) → False) ∧ (p3 ∧ (False → True))) ∧ p4) ∨ p1) ∨ (False → p2))) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243791708357874151766639137809 : ((p5 → p5) ∧ (((p5 ∧ (False → p4)) ∨ False) ∨ (((((p3 → p2) → False) ∨ False) ∧ (p5 ∧ p2)) ∨ ((p2 → p2) ∨ (p4 ∧ (p1 ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257874859094736728075267463868 : ((p4 ∨ True) → (((p4 ∧ (((p5 ∨ p4) → False) ∧ ((p3 → p4) ∨ True))) → p3) ∧ (((p3 ∨ p1) ∨ ((p2 ∨ p1) → (p1 ∨ True))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h19 : (p5 ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h20 := h5 h19
      -- False on the left can always be used.
      apply False.elim h20
  -- Implications on the right can always be decomposed.
  intro h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158697780797213163320257983642 : ((p2 ∧ (p2 ∨ ((((True ∨ ((p1 ∨ p3) ∨ (p3 → p4))) ∧ p5) → False) ∧ (True ∧ (True ∧ p4))))) ∨ (p4 → (p2 ∨ (p3 → (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134346341155833041085234086908 : (((p5 ∧ ((p3 ∨ p1) ∧ (p1 ∧ ((((((p2 → True) → p2) → p2) → p5) ∨ p5) ∧ ((p2 ∧ False) ∧ p4))))) ∨ True) ∨ ((p4 ∧ p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39035900337726206810727291691 : ((((p4 → p3) ∧ ((p2 ∨ True) → ((p5 ∧ ((True ∧ p2) ∨ p3)) ∨ (((p2 ∧ True) ∨ ((p3 → p2) ∧ (True ∧ p3))) → False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39910876108195710245174280335 : (((p3 → ((p4 → (False ∧ (p5 → ((((True → (False ∧ True)) ∨ (((p3 ∧ p2) → p1) → p3)) → (p2 ∨ p1)) → False)))) ∨ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37474335870769175839998225479 : ((((((p5 ∨ ((p4 ∧ False) ∨ p3)) ∧ True) → ((p2 → p2) → ((((True → p4) ∧ (p3 → p1)) ∨ False) → (p2 → False)))) ∨ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351003108745653415144000637750 : (p4 → ((p1 ∨ (((p5 → p1) ∧ p3) → ((((((p1 → p5) → (p1 ∨ (p1 ∧ p2))) ∧ False) ∧ (p4 ∧ p4)) ∨ False) ∨ p2))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642822751976607675959170851397 : ((((p2 ∧ ((((p1 → p4) → ((((p3 → ((p2 ∧ p4) ∧ p2)) → p1) ∨ p1) ∧ (True ∨ (False ∧ (p2 ∨ True))))) → p3) ∧ p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686640279987157914428874444413 : (((((False ∧ p5) → (p5 → ((p2 → ((True → p2) → p2)) ∨ (((p4 ∨ p2) ∨ p2) ∨ p3)))) → (p3 ∧ ((p5 ∧ (p5 ∧ False)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263275683187979860464825545436 : (True ∧ ((p3 ∧ (p4 ∧ (((p2 ∨ ((p1 ∨ p4) ∨ False)) → ((False ∧ p5) ∧ ((True ∨ (p4 → p1)) → (True → p5)))) → True))) → (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171927134613238129656300449666 : ((((p2 ∧ (False ∧ ((p4 → False) ∨ ((p5 ∨ p4) ∧ p5)))) ∧ p4) ∧ (p5 → p3)) ∨ ((p4 → ((False ∨ (p1 ∨ p1)) ∨ (p1 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185021309259149898014060983514 : (((p3 ∨ p1) ∧ (p2 ∧ (p1 → (p2 ∨ (p2 → (p2 → True)))))) ∨ ((((p3 → (p3 → ((p3 ∧ True) ∨ p4))) ∧ (p4 → p2)) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347115380097981530374232580032 : (p3 → ((True ∧ ((p4 ∨ False) ∧ (p4 → ((p2 → ((True → p3) ∨ p1)) → False)))) ∨ (True ∨ ((((p5 ∨ (True → True)) ∨ p4) → p5) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216463492187715873343389125406 : ((p4 → (True → (p2 → False))) ∨ ((True → ((p4 ∨ ((p2 ∨ p3) ∨ (((True ∧ p1) ∨ False) ∧ p5))) ∨ p2)) ∨ ((p3 ∨ p1) ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_116996074502049012021150184204 : (((True ∨ p3) → ((((p2 ∨ p4) ∧ (p5 → ((p4 ∧ True) ∨ p1))) ∧ p1) ∨ (p5 ∧ (p2 → (p5 → (False ∨ (p2 ∨ p4))))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119472218371067078529701622832 : ((p4 → (True ∧ ((False ∧ ((p3 ∨ (p3 ∨ p2)) ∧ ((False ∧ (((p3 ∨ p3) → p2) ∧ (p1 → False))) ∧ (p3 → p3)))) ∨ p4))) ∨ (p3 → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252535678081478502476684171084 : ((p5 → p2) ∨ ((((True → False) ∧ p1) ∧ (p3 → True)) → (((p1 ∧ (p5 ∨ (p2 ∨ ((p4 ∧ (True ∨ (p3 ∧ p5))) ∧ p5)))) ∨ p2) → p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h18 := h15 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h1.left
          let h26 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h25.left
          let h28 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h1.left
          let h33 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h34 := h32.left
          let h35 := h32.right
          -- One of the premise coincides with the conclusion.
          exact h21
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h39, we can now drive its conclusion.
    let h42 := h39 h41
    -- False on the left can always be used.
    apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353715731313929764442480454124 : (p4 → (True → (((p1 ∧ (False ∧ ((True ∧ ((False ∧ p4) → False)) → (False ∨ False)))) ∧ (((p5 ∨ p2) → (p4 → (p1 → p5))) ∨ True)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145790571240341992218306245690 : (((p4 ∨ p5) ∨ (True ∨ (p3 → (((((p4 → p4) ∧ p2) → p3) → ((False ∧ p2) ∧ (True ∧ p1))) ∧ p3)))) ∧ (((p2 ∧ p5) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174799276161093019141925499541 : (((p5 ∨ p4) ∧ (p1 → (p3 ∨ ((p2 → (p3 ∨ True)) ∧ (p2 → (p4 → False)))))) → ((((p2 ∧ (True → (p2 → p5))) → p5) → p1) → p1)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∧ (True → (p2 → p5))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 ∧ (True → (p2 → p5))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354680825173050719979574900058 : (p5 → (((((p2 ∨ ((p1 → p3) ∧ p4)) ∨ ((p4 → p3) → (p4 → p1))) ∨ (p1 ∧ ((False ∨ (True ∨ False)) ∨ p1))) ∧ (p5 ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191366349537564782529910423716 : (((True → p1) ∨ ((((False ∨ False) ∧ p5) ∨ p4) ∧ False)) ∨ (p3 ∨ ((False ∨ (False ∧ (p5 ∧ p3))) → ((p1 ∧ ((False ∨ p3) → p5)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40135064844067544178879951418 : ((((((True ∨ p4) ∨ ((p1 ∧ ((p4 ∨ p2) ∧ p3)) ∧ (((p1 → p3) ∨ p3) ∧ p3))) ∧ (((p4 ∧ p3) ∧ False) ∧ p5)) ∧ p3) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330828859225868220978933712748 : (True → (p2 → (p5 ∨ ((False ∨ (((p5 ∧ (p2 ∨ p4)) → p1) → (((False ∨ p4) ∨ p1) ∨ ((p4 ∨ (False ∨ (p1 ∨ p2))) ∨ p4)))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166458943096914284963599459440 : ((p2 ∨ ((True → p1) ∧ ((True → (((p4 ∧ (p4 ∨ (p1 ∨ p4))) → p2) ∧ p5)) → p2))) ∨ ((((True ∨ (p3 ∧ p1)) ∨ p3) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328106051306190292198120542078 : (True → (((((False → p2) ∨ (p2 ∨ p3)) → ((((((p5 → True) ∧ p2) → False) → p5) → p4) → (p4 → p2))) → p1) ∨ (p5 ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_682459899993484199977101278686 : ((((((p5 → p1) ∧ (p2 ∧ ((False → p1) ∧ ((True → p2) ∧ True)))) ∨ (p1 → (p5 → True))) ∧ (p4 → (((p1 → p2) ∨ p1) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785527535240281883314260236332 : (((p4 ∨ ((p4 ∧ (p2 ∧ ((((p3 ∨ p1) → (p4 ∧ ((p1 → p3) ∨ p1))) ∧ (((p5 ∧ True) → (p2 ∨ p2)) → True)) ∨ p5))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184872128150137514174642349998 : ((((p1 → p3) → False) ∧ (((p3 ∧ (p5 → True)) → p1) ∧ False)) ∨ ((True ∧ (((p3 ∨ ((p2 ∧ (p4 ∨ p3)) ∨ True)) ∧ p2) → p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59967601453394948153395919469 : (((True ∨ p5) → (p3 ∨ (p4 ∨ ((((p5 ∨ p1) ∨ ((p5 ∧ (p1 → ((p1 ∧ p5) ∧ (p1 ∨ p4)))) → p4)) → p5) → (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306345890020796065435021048484 : (p1 ∨ ((p5 ∨ True) ∧ ((((((((p2 → p5) → False) → p2) ∧ p5) → False) ∧ (((p3 ∧ False) ∧ p3) → (p3 → p1))) ∧ p5) → (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((((p2 → p5) → False) → p2) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h6
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684295074112586213596946732042 : (((((p2 ∧ ((p4 ∧ p3) ∨ ((((p1 → p4) → False) → p2) ∨ p3))) ∨ ((p3 ∨ False) → True)) ∨ (((p5 ∧ p2) ∧ (p5 ∨ p3)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_113014570247634168195113604584 : (((p5 ∧ (((p2 ∨ (p3 ∨ ((p1 → True) ∧ ((p5 ∨ p5) ∨ p1)))) ∨ (False → (p3 ∨ p1))) ∨ (True ∨ (True ∧ p2)))) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336440771612898360234428744254 : (p1 → ((p4 ∨ (((((p4 ∧ ((p1 ∨ p1) ∨ p5)) ∧ p3) ∨ (p5 ∧ False)) ∨ (((p1 ∧ (True ∧ p3)) ∨ p5) ∧ (p1 ∨ p2))) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43025545439665409568154933719 : ((((((p5 → ((True ∧ (((((p3 → True) → p5) → p2) ∨ ((p1 ∨ p1) → (True → p5))) ∧ False)) → p4)) ∧ p4) ∨ False) ∧ p1) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697039668031980862123068812859 : (((((True → (((p3 ∨ p4) → True) → p3)) ∨ ((p2 → True) ∧ True)) ∧ ((p1 ∧ (p3 ∧ (p5 → (p2 ∧ p2)))) → (p2 ∨ (p2 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353411364556034136183640968075 : (p4 → (p1 ∨ (((((p1 ∨ (p4 → p5)) → (((p3 ∨ p3) ∧ p2) ∧ ((False ∨ (p2 ∨ p2)) ∨ p3))) → (p3 ∨ p2)) → (p5 ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302558706030043579631845176833 : (False ∨ (p1 ∨ (((True → (((p5 ∨ p5) ∨ p4) → (p3 ∨ (True → True)))) ∧ ((p2 ∧ (p3 ∧ (p1 → (p2 ∨ p2)))) ∨ (p1 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758885571022989159980277764934 : (((p2 ∧ (((False → ((((((False → ((False ∧ p1) → False)) ∨ p5) ∨ p5) ∧ False) → (p4 ∨ (p5 ∧ p5))) ∨ False)) ∧ (p1 ∨ p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329262234767951355466497774780 : (True → (((p4 ∨ p4) ∧ p4) ∨ ((p4 ∨ (p4 ∨ p3)) → ((((p4 → True) → p4) ∧ p2) → (((p3 ∨ p1) → True) → ((p1 ∨ p2) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h13 : (p4 → True) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h15 := h7 h13
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h23 : (p4 → True) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h25 := h17 h23
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219497127464294476168018682231 : ((p5 ∨ ((True ∨ p4) ∨ False)) → (((p4 ∧ False) → ((p5 ∧ ((p3 ∧ ((p2 ∨ p2) ∧ p3)) ∨ p4)) ∨ False)) → ((p1 ∧ (False ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172692498506153832869393428251 : (((p3 ∧ p3) ∨ (p2 ∧ (True ∧ ((p1 ∧ (False → p5)) ∧ (p4 ∧ (p3 ∧ p1)))))) ∨ ((p3 ∨ p1) ∨ (False → (((True ∨ p3) ∨ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215428211905015029580825638039 : ((p3 ∧ ((p2 ∧ p4) ∨ p4)) ∨ (p2 → ((p4 ∨ ((False ∨ (p4 → p2)) → ((p1 → True) ∨ ((p3 → False) → ((p4 → p5) → p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754612305739204173315334417501 : (((False ∧ (p3 ∧ ((p3 ∧ (False ∧ (((False ∨ ((False ∨ (p4 ∧ ((p3 ∧ p4) ∨ p2))) ∨ (True ∧ (p1 ∧ False)))) → p2) → p2))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190896439864422134115465288434 : (((p5 ∧ (p5 → ((p5 ∧ True) ∧ False))) → (p4 ∨ False)) ∨ (p2 → (True → ((((p3 ∧ p5) → p4) → (p4 ∧ p3)) → ((p5 ∨ p3) → p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615535851778398826389238575556 : (((((((p2 → p3) → ((False → p5) ∧ p4)) → (p1 → ((True ∧ (False ∨ True)) → p3))) → ((p5 ∧ (True → p4)) → (p5 → p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_351470496128036143747317359282 : (p4 → ((p1 ∨ (p1 ∧ (((True ∧ p3) ∨ ((p1 ∨ ((p5 ∧ p2) ∧ (p5 ∨ p1))) ∨ p2)) ∧ (p1 → True)))) → ((p5 ∨ (p1 ∧ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h16.left
          let h19 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249251026896714935233218320200 : ((p4 ∨ p4) ∨ ((p5 ∧ ((p2 → ((p2 ∨ p1) ∨ ((p3 ∧ (p3 ∧ p3)) ∨ p2))) → False)) → ((((p2 ∧ False) ∧ (True → p5)) ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_84126894785138076068197920728 : ((((p5 ∨ True) → ((((False → (p2 ∧ p1)) ∨ (p1 ∧ p3)) ∧ p3) ∧ (p5 ∨ True))) ∧ (((False ∧ p2) → ((False → p2) → p1)) ∨ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1398407212251923074510398757 : (((((p1 ∨ (p5 → p4)) → (p2 ∧ p3)) ∨ p1) ∨ (((((p4 ∨ p2) → p5) → p5) → True) ∨ (True ∧ (p2 ∧ p1)))) ∧ (False → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638736344607481367492056446502 : ((((((p5 → p2) → (p5 ∨ (p4 → p1))) → (((False ∧ (True → (((p1 → p1) ∨ p2) ∨ p2))) ∧ p2) ∧ (True → (p4 ∨ True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179094688676506270240303434537 : ((False ∧ (((True → ((p4 ∨ p1) → True)) ∨ (p2 ∨ (False → False))) → p2)) ∨ ((False → (False → (False ∧ (True ∨ p4)))) ∨ ((p4 ∨ p3) → False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352793092950765809328711773325 : (p4 → ((p1 ∨ p3) → ((((p3 ∨ (p4 ∧ True)) ∧ ((((p1 ∧ p2) → (p4 ∨ p3)) ∨ p1) → p3)) ∨ (p4 ∨ (p4 ∧ (p4 → p5)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197490833894439051458914275575 : (((p1 ∧ (p3 ∨ (p2 ∨ p2))) ∧ (p5 ∧ p3)) ∨ ((((p2 ∧ (False ∧ ((p4 ∨ (p4 ∧ (p1 ∧ (p3 ∧ p2)))) ∧ p4))) → p4) ∧ False) → False)) := by
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
theorem thm_5_vars_52998563943110651566591669114 : (((((((p4 ∨ p4) ∨ p3) ∧ p1) → (True ∨ False)) → (p3 ∨ p2)) ∧ (((p4 → p1) → ((p5 ∨ ((False ∧ p5) ∨ p5)) ∧ True)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114901242810834771246875402872 : (((p3 → (((True → p4) → (True ∧ False)) ∨ (p2 → ((p4 → p2) ∧ p5)))) ∨ (((((False ∧ p5) ∧ True) ∧ p1) ∨ True) ∨ p5)) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157393747360410178510863733697 : (((((((False ∨ p1) ∧ (p1 ∧ ((p3 ∧ p3) ∧ p2))) → p5) ∨ (True ∧ True)) → p5) ∧ (True ∨ True)) ∨ (True ∨ (p3 → (p4 ∨ (p2 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249294669300886254796380752441 : ((p4 ∨ p5) ∨ ((((((p2 ∧ True) → ((p3 → False) → False)) ∨ (p3 → ((((p4 ∨ p2) ∧ (False → True)) ∨ p5) ∨ p3))) → False) ∨ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p2 ∧ True) → ((p3 → False) → False)) ∨ (p3 → ((((p4 ∨ p2) ∧ (False → True)) ∨ p5) ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811684346106253350030296749914 : (((p5 → (p2 → ((p3 ∧ p5) → ((((False ∧ ((p2 ∨ p3) ∧ p4)) ∨ (p1 ∧ p5)) ∧ ((p4 ∧ True) ∨ ((True → p2) ∧ p1))) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149357677955105717932279354089 : (((p5 ∨ p1) → (p5 ∨ (((True → ((True → (p3 ∨ (p3 ∧ p2))) ∧ p3)) ∨ (p5 → (True → p5))) ∧ p2))) ∨ (p5 ∨ (p2 ∨ (False → p4)))) := by
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
theorem thm_5_vars_609959440717450559308129077675 : (((((p5 → (((False ∨ (p1 ∧ (p1 → (p5 ∧ p3)))) ∧ (p4 ∨ p2)) ∨ (p5 → ((False ∨ p3) ∧ (False ∧ (p5 ∧ p1)))))) ∨ p4) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_171927202155059437813253127607 : ((((p3 ∧ (((p5 ∧ (p1 ∧ p5)) ∨ p2) ∨ (p2 → p5))) ∧ p3) ∧ (p3 ∨ p1)) ∨ (True ∨ (p4 → (p4 ∧ (((p3 ∧ p3) ∧ False) ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255684772600581469591982875192 : ((p5 ∧ p5) → ((p2 ∧ (p1 ∧ (p3 ∧ (((p5 → ((False → False) ∨ (p5 ∧ (p4 ∨ p5)))) ∧ p1) ∨ p2)))) ∨ ((p4 ∧ (p5 → p3)) ∨ True))) := by
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
theorem thm_5_vars_344486765786208049412207957556 : (p2 → (True → ((p4 ∧ (((p1 ∧ (False ∧ ((p3 ∧ (p5 ∧ False)) ∨ (p3 ∧ (False ∨ False))))) ∧ True) ∨ p4)) ∨ (((False → False) ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191247401831741966224943178337 : (((p1 ∧ p1) ∧ (((p4 ∨ (p4 ∨ p5)) ∨ p4) ∨ p1)) ∨ ((p2 → True) → (((True ∧ (False ∨ (((p4 ∨ True) ∧ p5) ∨ p4))) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313107663014280899547327353349 : (p3 ∨ ((((((p2 ∧ (True ∧ (False ∨ (p3 ∨ p2)))) ∧ ((p1 ∧ (p5 ∨ p2)) → (p2 → p3))) ∧ p2) ∧ True) ∨ ((p2 ∨ p1) → True)) ∨ p1)) := by
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
theorem thm_5_vars_788418377577806324883225664301 : (((p5 ∨ (((((((True → True) ∨ p4) ∨ p5) → (p2 → False)) ∧ p5) ∧ (((True ∧ p2) ∨ (((p4 → p3) ∨ p5) ∨ False)) ∧ p4)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158783055908387954672439027613 : ((p5 ∧ (((((p4 ∧ ((p4 ∨ False) → True)) ∨ (p3 → p1)) ∧ p3) ∨ (p1 ∨ (p4 → True))) ∨ True)) ∨ (((p4 ∧ p3) ∨ (p5 → p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307809785862890108203244075790 : (p1 ∨ (p4 → ((((((p5 ∨ True) ∨ p2) → p3) → ((p3 → False) ∨ p3)) ∨ p3) ∧ (p5 → (p5 → (False → (((False ∧ False) ∧ True) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h7
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686087055321440136357205851702 : (((((((False → p3) ∧ (p5 → True)) ∧ (p5 → (p3 ∨ (p3 → p3)))) ∧ (p2 ∨ (p5 ∨ p4))) → ((((p5 ∧ p2) → p2) → p5) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665918534196427560644758819328 : ((((((p5 ∨ (p4 ∧ (p5 ∧ p1))) ∨ (p5 ∨ (((p1 → (False ∧ True)) → p4) → (p5 ∨ (p5 ∨ p5))))) → False) ∧ (False ∧ (p3 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809672809956901725898129232467 : (((p5 → (((((p1 → p2) ∧ ((True ∨ ((p2 → p5) ∨ p2)) → (((p1 → True) ∧ (True ∨ p3)) ∨ p1))) ∧ p2) ∨ p4) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591939239636711186429729520105 : (((((((p1 → False) ∧ p3) ∨ ((((False → (p2 ∨ (p1 → (p3 → (p2 ∧ p5))))) ∨ (True → p2)) → p4) → p1)) ∨ (p3 ∨ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258182927921937092357168118445 : ((p4 ∨ p4) → ((((p5 ∧ False) ∨ (p5 ∧ p2)) ∨ p4) ∨ (((p4 → ((p2 → ((p4 ∨ p1) ∧ p3)) → ((p2 ∧ p4) ∧ p5))) ∧ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626713932580206769814743784606 : ((((p5 → (((True → p5) → (p5 ∧ ((p1 ∧ (p5 ∧ (p3 → True))) → (p3 ∧ ((p5 ∨ (False ∨ (p4 → p3))) ∨ p2))))) ∨ True)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_98613898494780651140973624641 : ((p5 ∨ ((p3 → (p1 ∨ (p5 ∧ p3))) ∧ (((p1 → (p5 ∨ ((p5 ∧ p4) ∧ p1))) ∧ ((True → (p5 → (p1 → p4))) → p2)) ∧ p3))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198392535969614887087992789632 : ((p3 ∧ (p5 ∧ (p4 ∧ ((p3 ∧ p5) → p4)))) ∨ ((p1 ∨ ((p5 ∨ p5) → p5)) ∧ (True ∨ (p3 ∧ (True ∧ (p2 → ((p2 ∨ p1) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50866157036270458031111965086 : ((((True ∧ (False ∨ (((p3 ∧ p5) ∨ (True ∨ (False ∧ ((p1 ∨ p4) → p4)))) ∧ p1))) ∨ p2) ∧ (p3 ∧ (((p2 → True) → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977141038136073002870211841181 : (((True ∧ ((((True → ((False ∨ p5) ∧ (False ∧ (False → p4)))) ∨ ((p5 ∧ p1) → p5)) → False) ∧ ((p2 ∧ (False ∨ False)) ∨ (p4 ∨ False)))) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : ((True → ((False ∨ p5) ∧ (False ∧ (False → p4)))) ∨ ((p5 ∧ p1) → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h13
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698931308445033319949024434997 : ((((p4 ∧ ((((p5 → False) → p1) ∧ ((p1 → p4) ∨ False)) ∧ p3)) ∨ (((p4 → False) ∨ (p5 ∧ False)) ∨ (p1 ∨ ((True ∧ p4) → True)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234509035596512693617096517707 : ((p2 → (p1 → False)) → (p2 → (((p1 ∧ (p3 ∨ p1)) ∨ p3) ∨ ((((p4 ∨ (p4 ∨ p5)) ∧ (p3 → (p2 ∨ p4))) → p3) ∨ (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230220862260088123436354676863 : (((True ∨ p1) ∧ p3) → (p3 ∧ ((False ∨ (((True ∨ ((p4 ∨ p3) → p4)) → (False ∨ (p3 ∨ p5))) ∧ (p4 → ((p3 ∨ False) → True)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790010717464944276342923600565 : (((p5 ∨ ((p1 ∧ True) ∨ ((((p2 ∨ False) ∨ p5) ∨ p2) ∨ (p1 → (True ∧ ((((True → p2) ∨ (p1 ∨ (True → True))) ∧ True) ∨ True)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55454779868454608059244188722 : ((((False ∨ (False ∧ (True ∨ p3))) → p3) → ((p2 ∨ ((p1 ∧ (p4 ∨ (False ∨ p4))) ∨ (((p3 ∨ p4) → (True → p2)) ∨ p2))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349125247055908228909672657281 : (p3 → (True → ((False ∧ p2) ∨ (p1 → (p5 ∨ (p4 ∨ (((p5 ∧ (p1 ∨ p5)) ∧ (p3 ∨ p4)) ∨ ((p5 ∧ (False ∨ (p1 → False))) → p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115874181800615212409916326919 : (((((p2 ∧ p5) → p5) ∧ p2) ∨ ((((((p5 ∧ p2) → (p2 → True)) → ((p1 ∨ (False → p3)) ∧ True)) → p2) → p5) ∨ True)) ∨ (p5 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



