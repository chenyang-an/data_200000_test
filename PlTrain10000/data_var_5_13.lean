variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63292521045792354560639846136 : ((p5 ∧ (((True ∨ p4) ∧ p3) ∨ ((p3 → (True → False)) ∧ (True → (p3 ∨ (((p3 ∨ p1) ∨ ((p3 → p4) ∧ p1)) ∨ (p1 ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308599488656187559936018083701 : (p2 ∨ (((p1 ∨ (True → p1)) → ((((((p4 ∨ p2) ∨ True) → p3) → ((False ∧ p3) → (p5 ∧ p3))) ∧ (p4 ∨ False)) → (p5 ∨ True))) ∨ p5)) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
theorem thm_5_vars_190974452239297337041404895742 : ((((p5 ∨ (p1 ∧ p1)) ∧ p4) ∨ ((p2 ∧ p5) ∨ True)) ∨ (((p5 ∧ p2) ∨ (((((p2 ∨ p4) → p3) → False) → True) ∨ p4)) ∧ (False ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40027357867136776532103607924 : (((((((((p5 → p2) ∧ (((((True ∨ True) → False) ∧ (p2 ∧ p5)) ∨ p2) ∨ True)) ∨ p4) → (True ∨ p3)) → p1) ∧ True) ∧ p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679974637930684461574651992326 : (((((((((p5 ∧ p2) → True) ∨ p5) ∧ (p5 → p1)) ∨ ((((p1 ∧ p3) ∧ p3) → False) ∧ False)) → p5) → (p1 → (p5 ∧ (p4 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54202991299684687433357770071 : (((((False ∧ p3) ∨ ((p1 ∧ p1) ∧ True)) ∨ p2) ∧ ((p1 ∨ (p4 ∧ p5)) → ((False ∧ p1) ∨ (((False ∧ True) ∨ (p4 → p5)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139852743097092918402913417716 : (((p5 → (((((True ∧ p2) ∧ ((p4 ∧ (p5 ∧ (p3 ∨ p2))) ∨ p3)) ∨ (p5 ∨ (p4 → p4))) → p3) ∨ p5)) → False) → ((p3 ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((((True ∧ p2) ∧ ((p4 ∧ (p5 ∧ (p3 ∨ p2))) ∨ p3)) ∨ (p5 ∨ (p4 → p4))) → p3) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55155834949970343605079988589 : (((((p1 ∨ p5) → (p2 ∧ p5)) ∨ False) ∨ (p3 ∨ (True → ((((p2 → p5) → p3) → p5) ∨ ((p3 ∨ p4) ∨ ((p5 ∧ p5) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149352873776649977724188861078 : (((p4 ∨ p1) → (((p3 → (p1 → (p2 → p2))) ∧ (p1 ∨ (((True ∧ p1) ∨ p3) ∨ p1))) ∨ (p3 ∨ p4))) ∨ (p1 ∧ ((p3 ∧ p4) ∧ p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615394644665868885651488498977 : (((((True ∧ (p1 ∧ ((False ∧ p3) ∧ (((True → (p2 → (p4 → p2))) → p2) ∨ p3)))) ∨ (True ∨ (((p5 ∧ True) ∨ p2) ∨ p1))) ∨ False) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61048543912488438796771044400 : ((False ∧ ((((p4 ∧ p1) → ((p4 ∨ (p5 ∨ (True → ((p2 ∨ p1) → False)))) → ((p2 → p2) → p1))) ∧ (p1 → p3)) → (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134575065705962320314456143690 : (((((p5 → p3) ∨ (((p5 ∧ p4) ∧ (((p3 ∧ True) ∧ (p5 ∨ p5)) ∨ True)) ∧ (p5 ∧ True))) ∧ (p1 → p1)) → p5) ∨ (True ∨ (p2 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55877372346735223069429374360 : (((False ∨ ((p3 → p5) ∧ p4)) ∧ (p4 ∧ ((p2 ∨ (p3 → p5)) → (((True ∧ ((p5 → (p1 ∨ False)) ∨ p3)) ∨ (p5 ∧ p5)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38058790664237842583863433501 : (((((((p3 ∨ (False → (True ∧ p5))) → ((p4 → p1) ∨ p2)) → (True → p1)) ∧ (p5 ∨ ((False → True) ∨ p2))) → (p5 ∧ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308687764500410033488180004472 : (p2 ∨ ((p1 ∨ ((((p5 → (True → p2)) ∨ (p1 ∧ p4)) ∧ p3) ∨ (p4 → (p5 → (((p1 ∨ (p2 ∨ False)) ∨ p4) ∨ (True → p2)))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113618337289939968475976496686 : (((True → ((p3 → (p1 ∨ (False ∨ ((p5 ∧ p4) ∧ p3)))) → ((((p3 → (p1 ∧ p2)) → True) ∧ p1) → p5))) ∨ (True → p4)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177709469335346605733042023739 : ((((((p5 ∨ True) ∧ p5) ∨ (p3 ∧ p2)) ∧ (p3 ∧ (p4 ∧ p1))) ∧ p4) ∨ (((False ∨ p4) ∧ ((p3 ∨ p2) ∨ p2)) → (False → (p4 → p2)))) := by
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
theorem thm_5_vars_64789604173643559446146345381 : ((p2 ∨ (((p3 ∨ ((p4 ∨ p1) ∨ (p2 ∧ (p5 ∧ (p4 ∧ (False ∧ True)))))) → ((False ∨ p4) ∨ (False → (True ∨ (p4 ∧ p2))))) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184386110299510463469917511562 : (((p2 → (((p5 ∨ p1) ∧ (p2 ∧ (p1 ∨ p1))) → p5)) → p3) ∨ (p3 ∨ (((p1 → ((p1 ∨ p3) ∨ p2)) ∨ False) ∨ ((True → p3) ∨ p2)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187424990453008643375519072342 : ((p5 ∧ ((p5 → (p2 ∨ (p5 ∨ (True ∨ p2)))) ∨ (p5 ∨ p1))) → (((p2 ∨ False) ∨ (p5 ∧ p2)) ∨ (((True ∧ p5) ∧ p4) ∨ (p5 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607868628500908318339679839375 : (((((True → ((p1 → ((p2 ∧ (((p3 → (p3 → p5)) ∨ p4) ∧ p2)) ∨ ((p1 → (p5 ∨ p2)) ∨ (p1 ∨ p3)))) ∨ p5)) ∧ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_171428270010870563146819365598 : ((((p5 ∧ True) ∨ (p3 → (p2 ∧ (p2 → ((False ∨ p4) ∨ (p1 ∧ p2)))))) ∧ p4) ∨ ((p1 ∨ (p5 → (False ∨ (p1 → p1)))) ∨ (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304774880993609497123688091922 : (p1 ∨ ((p3 ∨ (((p3 ∧ (((p1 → p2) ∨ p3) ∨ False)) ∧ (((p2 ∧ p3) ∨ (p5 → ((True ∧ p3) → False))) ∧ p2)) ∧ p3)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117477513713169256727069528861 : ((p1 ∧ (False ∨ ((p2 ∧ (True → (p3 ∨ (p3 → ((p3 → p1) → ((False → True) → (p4 ∧ (p2 ∧ (p3 ∨ p5))))))))) → p5))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200285331223006157303284950956 : (((p3 → (p3 → True)) → ((p3 ∨ p3) ∧ p2)) → (((p1 ∨ (((False ∨ (p5 ∧ (True ∧ p4))) ∧ ((p2 ∨ p1) ∧ p2)) ∧ p3)) ∨ True) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p3 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62267954374103162462034021030 : ((p3 ∧ ((((((p4 → (p2 ∧ ((p3 ∧ p5) → p2))) ∧ ((p2 ∨ (p2 → p5)) ∨ False)) → p4) → ((p1 → p3) → p3)) → True) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59228725507814058899943274657 : (((p2 ∨ False) ∨ ((p1 ∨ ((((True ∨ (True → (False ∧ False))) ∧ p4) → p1) ∨ p3)) ∨ (p4 ∨ ((p3 → ((p2 ∨ p1) → p4)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158893931154542685851334227682 : ((p1 ∨ ((((p4 ∧ ((p1 ∧ p5) → p4)) → (p5 → (((p3 → p1) ∨ True) ∨ p1))) ∧ p3) ∨ True)) ∨ ((p3 ∧ ((p1 → p4) → p3)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217141555202712117710502086033 : ((((p1 → p5) ∨ p2) ∨ True) → (((p1 ∧ (((p3 ∨ (p1 ∨ p3)) → True) → p1)) ∨ True) ∨ ((False → ((p4 ∧ p5) → (p4 ∧ p1))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689421201517582724272107895828 : ((((((False ∧ ((((p5 ∧ p2) ∨ p5) → p5) ∧ p4)) ∨ p5) ∧ (True ∧ (p1 ∧ False))) ∨ (p4 → (True → ((p4 → (p3 ∧ p3)) ∨ p4)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55776720200032263787420888354 : ((((True → p5) ∧ (True → p5)) ∧ ((p5 ∧ (((p3 ∧ p5) ∧ (((True ∧ p4) ∨ False) → (False ∨ False))) → p4)) ∧ (p1 ∨ (p2 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42684658513792257440123759701 : (((p5 ∨ (((p2 → (p3 ∧ (p2 ∨ False))) ∨ (((False ∨ p3) ∧ (p5 → (p5 ∨ True))) ∧ ((True ∨ p5) → (p1 ∧ p2)))) ∧ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136021042167042301227291397139 : ((((True → ((p5 ∨ (p4 ∨ (p5 ∨ False))) ∨ p4)) → p4) → (((p4 → False) ∧ p2) ∨ ((p2 ∨ p5) → (True ∨ False)))) ∨ (p4 → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347561812815383880828135991099 : (p3 → (((p3 ∨ p3) ∧ (True ∨ p4)) ∧ (((((((False ∨ p4) ∧ p5) ∧ p1) ∧ p3) → (True ∧ False)) → p1) ∨ (p1 → ((p5 → True) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350160398575041663175288219580 : (p4 → ((((False → ((p3 ∨ p3) ∧ (True → p5))) → False) ∨ ((p5 ∨ p4) → (p4 → (True ∧ (p1 → (((p3 → True) → p1) ∧ True)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58188740638880359754658169758 : (((p3 ∧ p4) ∧ ((((False → p2) ∧ (p5 ∧ True)) ∧ (True ∧ p5)) → (((p4 ∧ (((True ∨ p2) ∧ p1) ∧ (p3 ∧ True))) ∧ p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42034194298761185595942311325 : ((((p3 ∧ p4) ∨ ((p2 ∨ p1) ∧ (False ∨ ((((p4 ∧ True) ∨ p2) ∨ ((p4 ∧ p4) ∧ (p2 ∨ (False → (p3 ∨ False))))) → p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327835826467283764687406401527 : (True → (((((((p5 ∨ p5) → (True → ((p5 → False) ∨ False))) → p5) ∧ p2) ∧ (p4 ∨ p1)) ∧ (((p4 → p3) ∨ True) ∨ p1)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207001640436310354673086372204 : ((((True ∧ False) ∨ (p3 → False)) ∧ p3) → ((((p3 → (p1 → (p5 ∨ (p1 ∧ p5)))) ∨ p5) ∧ False) ∧ (((p4 ∧ p1) ∨ (p5 → False)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h1.left
    let h32 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
      have h37 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h36, we can now drive its conclusion.
      let h38 := h36 h37
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41300760800369860209757555277 : ((((p5 ∨ ((((p4 ∨ False) ∧ (p2 ∨ p2)) → True) ∨ (((p3 ∧ p4) ∨ (p2 ∧ True)) ∧ False))) → (p5 ∨ ((p5 → p5) ∧ p1))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116212434021244249359177657241 : ((((p2 ∧ False) ∨ False) ∨ (((p1 → (p3 → (p5 ∧ p1))) → False) ∧ (p5 ∧ ((False ∨ ((p4 ∨ p4) ∧ (p1 ∨ p1))) ∨ p3)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190351420898525807905292681854 : (((((p1 ∧ p2) ∨ p2) → ((p4 ∧ False) ∨ p5)) ∨ True) ∨ (((True → p2) ∧ p3) ∧ ((p3 ∨ (True → ((p2 ∧ p2) → (p2 ∧ p3)))) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194218598717431484922052291699 : ((p3 → (False ∨ ((((p3 ∨ True) ∨ p4) → p1) ∧ p4))) → (((p4 ∧ p3) → (True ∨ p2)) → (p2 ∨ ((((p4 ∨ p2) → p2) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39280119664652196859394262418 : (((p1 ∧ ((True ∧ ((p4 ∨ (p4 ∨ ((False → (p5 ∨ (p3 ∨ (False → (p2 → (p1 → False)))))) → (p5 ∧ True)))) ∨ p2)) ∨ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306210858629076363514569986175 : (p1 ∨ (((False ∨ p2) ∧ p2) → (p5 ∨ ((((p2 → p2) ∧ ((p2 ∧ True) → p3)) ∧ (False ∨ True)) → ((False ∧ ((True ∧ p4) ∧ p4)) ∨ p3))))) := by
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
    apply False.elim h4
  case inr h5 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : (p2 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h13
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775045016327239161734009609158 : (((False ∨ ((p3 → (p4 → p4)) → (p4 → ((p2 ∧ (False → p2)) ∨ (p4 ∧ (p1 ∧ ((((False ∨ False) ∨ p4) → p4) ∧ (p2 ∨ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301220517426918663576625471324 : (False ∨ (((True → p4) ∨ ((True ∧ False) → p1)) ∧ (((p4 ∧ True) ∨ ((p2 ∨ p3) ∨ ((p1 ∧ (((True ∨ True) → p3) ∧ p1)) → p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61091573190850340270596288020 : ((False ∧ ((True → (p1 ∧ (((False → True) → ((p4 ∨ True) ∧ p4)) → ((p3 ∨ p2) ∧ p4)))) ∧ (p3 → (False ∧ ((p2 ∨ False) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308605366739108442582947793411 : (p2 ∨ (((False ∨ True) ∧ (((((False → p3) ∧ (p3 → (((p2 → p1) → p5) ∨ (False → (p2 → p5))))) ∨ (p4 → p4)) ∨ p3) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147805309580071970253614255789 : (((p2 ∧ (p2 ∧ (p4 → ((p1 ∧ (((False → (p1 → p5)) → False) ∧ p1)) → ((p5 ∨ True) ∨ False))))) → p1) ∨ (((p1 ∧ False) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780305419713368764931547327965 : (((p2 ∨ ((((((p4 ∧ (True ∧ p3)) ∨ True) → False) ∧ (((p5 → p4) → (p1 ∧ p4)) → p5)) ∨ True) ∨ ((p5 → False) → (p2 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732931172966876554960031212946 : ((((p2 ∧ p2) ∧ (((p2 ∨ False) ∨ ((p4 ∨ p3) ∨ p3)) ∨ (p1 ∨ (((p2 ∨ (((False ∧ p2) ∨ p1) ∨ p1)) → (False ∨ p5)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201254938425033531077830808942 : ((p3 → ((p5 ∨ ((False ∨ False) ∨ False)) → p3)) → (((p1 ∧ ((p3 ∨ p2) → (p4 ∧ (False ∨ p1)))) ∨ (p1 → p1)) ∨ (True → (p3 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324882417241208616956647476723 : (p5 ∨ ((p5 → p5) ∧ ((((p4 → (p1 ∧ (p1 ∧ True))) ∧ p5) ∨ False) → ((p4 ∧ (False ∨ (p3 ∨ ((p1 ∧ p2) ∧ (p4 ∧ True))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3018049944094789544769766721 : (((p5 ∨ p3) → True) → ((((p3 ∨ (((p3 ∧ p5) ∨ p5) → p4)) ∧ (p1 ∨ ((p2 ∨ p3) ∧ (False ∨ p3)))) → (True ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152995141638983134294602096963 : ((p1 ∧ (False ∨ ((((((True ∨ True) ∨ p3) ∧ p4) ∨ p2) ∨ (p5 ∨ (False → (p1 ∧ (p5 ∨ True))))) ∨ p4))) → (p5 ∨ ((p2 → True) → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h13
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h15
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824313495132876161275288021568 : (((((p3 → (True → (p1 ∧ p1))) → ((p4 ∧ (True ∨ p5)) ∧ (p1 ∧ (p5 ∧ (True ∧ (False ∧ ((p3 ∧ p4) ∨ (False ∧ False)))))))) ∧ p1) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (True → (p1 ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44841405903581753670625166424 : (((((p2 → p5) ∨ p3) ∨ (((True ∨ p3) ∧ (p3 → (p1 ∧ ((p1 → (p5 → True)) ∨ (p3 ∨ p3))))) ∨ (p3 ∨ (p4 ∧ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303916444503017501836178471257 : (p1 ∨ (((True → (p2 ∨ ((p1 ∧ (True → ((p3 ∧ p2) → p2))) ∧ p4))) → (p5 → ((p3 ∨ (p2 ∨ p3)) ∨ ((p1 ∧ p5) ∨ True)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141707511735266058658595890724 : (((p1 ∨ p2) ∧ (p3 ∨ (((p4 ∧ (((p2 → (p4 → p1)) ∧ p1) ∧ (p5 ∨ (p3 ∨ p5)))) ∧ (False → p5)) ∨ True))) → (p2 → (p5 ∨ p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h30.left
        let h33 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h34 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h37
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52793173393812916594538717765 : (((((((p5 → p5) → p4) ∧ p5) ∧ (p5 ∨ p5)) ∧ ((p3 ∨ p2) → p1)) → (p2 ∧ ((((p1 ∨ (False ∧ p1)) ∧ False) ∨ p4) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38872860992423639942707087554 : ((((p2 → (p4 ∨ True)) ∧ ((p1 ∨ (((p4 ∧ False) → (((p2 → ((p5 ∨ p5) ∨ p5)) ∨ True) ∧ True)) ∨ p3)) → (p2 → p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173069998071969753570016681907 : ((False ∨ (p2 ∨ ((p3 ∨ ((p1 ∨ (p4 ∧ True)) → p2)) → ((True ∧ p5) ∧ False)))) ∨ (((True ∨ False) ∨ (p2 ∨ True)) ∨ ((p1 → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877101581328769404848928238047 : (((((((((True ∨ False) ∧ p1) ∨ p5) ∨ (p5 ∨ p1)) → (p2 → p2)) → ((p1 ∧ False) ∧ ((p5 ∨ (p1 ∨ p5)) ∨ p2))) ∧ (p4 → p4)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ False) ∧ p1) ∨ p5) ∨ (p5 ∨ p1)) → (p2 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h17 := h2 h4
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649991230001538118244671350363 : (((((((p5 ∨ True) ∧ p2) ∧ (p1 ∨ (p2 ∧ (p4 ∨ (p5 → ((p3 → p1) ∨ (p2 → True))))))) ∨ ((False ∧ p3) ∨ True)) ∧ (True ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56101303276210768921370870866 : ((((p4 ∨ p3) ∧ (p1 ∧ False)) ∨ (p4 ∨ (((True ∧ ((p1 ∧ (p3 ∨ True)) → p2)) ∨ False) ∧ (((False → p3) ∧ (p1 ∧ True)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125461541988127034738687161726 : (((True ∨ p4) ∧ ((False → (((p4 → (p1 ∧ (False ∧ p2))) ∧ (p1 ∧ (p3 → (True → (p2 ∨ (p4 → p3)))))) ∧ False)) ∨ p4)) → (p1 ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208602967571656732311687096318 : (((p4 → True) → (p1 ∨ (p2 ∧ True))) → ((p2 ∨ ((((p3 → (p4 → p1)) → ((p1 ∨ (True ∧ p2)) ∧ (True ∨ p3))) ∧ p1) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40427893087703711142743814655 : (((((((p3 → p5) ∨ ((p1 → p2) → (p3 → (False ∨ p4)))) → p5) ∨ (p1 ∧ (p3 ∧ (((True ∨ p3) ∧ p3) ∨ p4)))) ∨ True) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258913620060918918559602405247 : ((True → p2) → (((p2 ∨ p5) → (p4 ∧ False)) ∨ ((((True ∧ p4) → (p2 ∨ ((((p2 ∨ p4) ∨ (p5 → p4)) → True) → p4))) ∨ p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133942895959052227871440916740 : (((p1 → ((p5 → ((False → (p5 ∧ p5)) ∧ (p3 ∨ (((p3 → p2) ∧ (p4 ∨ (True ∧ p4))) ∧ True)))) ∨ p5)) ∧ False) ∨ (p3 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52243526082086005282714510629 : (((p5 ∧ ((False ∨ (p3 → p1)) → (p5 ∨ (p2 → (True ∨ (False ∨ (p5 ∨ True))))))) → (((p1 → (p1 ∨ (p4 → True))) → p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260427918598174239119434622468 : ((p3 → True) → ((False → (((p3 ∧ ((p5 → p1) ∨ False)) ∧ p5) → p4)) → (((p2 ∨ (False → p4)) ∧ ((p4 ∨ (True ∧ True)) → False)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ (True ∧ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346912715210189898006036497841 : (p3 → ((((p4 ∨ False) ∨ (True ∧ p2)) ∨ ((((True ∨ p5) → False) → p1) ∧ (False ∨ (False ∧ p3)))) ∨ ((False ∧ (p5 ∧ p4)) → (p1 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308507261485224976916963278596 : (p2 ∨ ((((((False ∨ (p4 ∧ (((p1 ∨ (True ∨ p1)) ∧ p3) ∨ p1))) ∨ True) → p4) ∧ (p5 → True)) → (p5 ∨ ((False ∧ p2) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303080133203603818191029008372 : (False ∨ (p2 → (True ∧ ((False ∨ (True → ((((p4 → p5) ∨ p3) → p1) → ((((True → p4) ∨ (p3 ∧ p5)) ∨ (p2 ∧ True)) ∨ p3)))) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228562930955528252812287374042 : ((p1 ∨ (False ∨ p4)) ∨ (p4 ∨ (((p4 ∧ (p3 → p4)) → (True ∧ (p2 ∨ (((p2 ∧ True) ∨ (False ∨ True)) ∨ (p5 ∨ (p2 ∧ p3)))))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_43992666852349177560634032234 : (((((p4 → ((((False → p2) ∨ (((p5 → (False ∧ True)) → ((p3 ∧ p3) ∧ p1)) ∧ p5)) ∨ p5) ∧ p5)) ∨ p5) → (p1 → p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193446553649335179889231668223 : (((p3 → True) ∧ ((True ∧ p5) ∨ ((p5 ∧ p1) ∧ p4))) → (((p3 ∧ p1) ∧ (((p1 ∨ ((p3 → p2) ∧ p3)) → p3) ∧ False)) ∨ (True ∧ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61389849316594723378031237877 : ((p1 ∧ ((((True ∨ ((False ∨ False) ∧ p3)) → (p3 ∧ p3)) ∧ (p1 ∨ (p1 → (p4 → (p3 ∨ ((p2 ∨ (p1 → True)) ∨ p4)))))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48554402224123245057648490527 : (((((((((p2 ∨ False) ∨ True) → False) ∧ (p2 ∨ p4)) ∨ (p4 → ((False ∨ p1) ∧ True))) ∨ (True ∨ True)) → p2) ∧ ((p5 → True) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350947339421092987807580380795 : (p4 → ((((((False ∨ p2) ∨ (((((False ∨ False) ∨ p2) → p3) ∨ p3) ∨ (False ∨ p3))) → p1) ∨ p2) ∨ (p5 ∧ (p5 → p2))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43455719620389345832439265391 : (((((p2 → p4) ∧ (True → ((p4 → (False ∨ (p2 → ((p2 ∨ (False ∨ (False → ((False → p3) → p4)))) ∧ False)))) ∧ False))) ∨ False) → p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174904509267832218445978736903 : (((p5 ∧ p5) → (((((p1 → p4) ∨ p3) ∨ p1) ∨ True) → (p4 → (False ∨ True)))) → (((p5 → False) ∨ p4) ∨ ((True ∧ True) ∨ (False ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246485266701356209748786110763 : ((p5 ∧ False) ∨ (p1 → ((((p5 → (((((p3 → p4) ∨ (p4 ∧ ((p1 ∨ True) → p3))) ∧ (False ∨ False)) ∧ p3) ∧ p2)) ∧ True) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156953952695662668889385724600 : (((((p4 ∧ p5) ∨ ((((p1 → (p1 ∧ True)) → p1) → False) ∨ True)) ∧ ((p5 → p4) ∧ p4)) ∨ p2) ∨ ((((p3 → p4) ∨ False) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177737251119842933852311492021 : ((((p4 → (p4 ∨ p5)) ∧ (p2 ∨ (((p5 ∨ p3) ∨ True) ∧ p2))) ∧ False) ∨ ((p2 ∨ False) → (False → ((p2 ∨ (p1 ∨ (p5 ∨ False))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135273844644547148784019232359 : (((p3 ∨ (((((p5 ∧ (False ∧ p4)) ∨ True) ∨ p2) ∧ (p5 ∧ (p1 → (True ∧ True)))) ∧ (True ∧ p2))) → (p1 ∨ p1)) ∨ (p2 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40637448995268327802248362154 : ((((((p1 ∨ (p3 ∧ (p4 → ((p1 → p5) ∨ p3)))) ∨ (((p2 ∧ False) ∨ (True ∨ (False ∨ p5))) ∨ (p2 → p2))) → p2) → p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135701813679593193909152433836 : (((((p1 → p4) → (p2 ∧ True)) → (p3 ∧ (((True ∨ p5) ∧ p5) ∨ p3))) ∧ (True ∧ (True → ((p2 → p2) → p5)))) ∨ ((p1 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346284873831522494994345556613 : (p3 → ((((False ∨ (True → (((p4 ∨ (p5 ∧ p2)) ∧ (p4 ∧ True)) → False))) ∧ (p3 ∧ ((True ∧ (p3 ∨ p5)) → p4))) ∧ True) ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260891212338070193707522380819 : ((p4 → False) → ((((p3 → False) ∧ False) ∨ ((((p4 ∨ (p1 ∨ (p5 ∨ p2))) → p5) → (p1 ∧ ((p2 ∧ True) ∨ p4))) ∨ (p5 → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45408471625031655144868543995 : (((p5 ∧ ((p1 ∨ p5) ∧ ((p4 ∨ (p2 ∨ (((p2 ∧ True) ∨ p1) ∧ ((p1 ∨ (p5 ∧ p4)) ∧ ((p4 → p4) ∧ p5))))) ∧ p3))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135029471235703865783051482910 : ((((((((((((p4 ∨ (p5 → p3)) → p5) → p1) → True) → p1) → p5) ∧ p4) ∧ True) ∧ p1) ∧ p2) ∨ (p1 → p4)) ∨ (p3 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338516930371786999425509550756 : (p1 → (((False ∨ False) ∨ p2) ∨ ((False ∨ False) ∨ ((((((p5 ∧ ((True ∧ p5) → p4)) ∨ p4) ∨ True) → p1) ∨ (p1 ∧ (p4 ∧ p2))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548348488031331898851549652281 : (((False ∨ ((False ∨ (p1 ∧ (p1 ∨ p2))) ∨ (((p4 → (p1 ∧ (p5 → (p2 ∨ (p1 → (p2 ∨ (False → True))))))) ∧ True) → (p5 → p5)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137251130070725089566738629294 : ((p1 ∧ ((p2 ∧ (False → (p3 → p4))) ∨ (((p4 ∨ True) ∨ p2) → ((p3 ∧ (p1 → (True ∨ p1))) → (p4 ∧ p1))))) ∨ (p3 → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358459913412755234377942127426 : (p5 → (p1 → (((False ∧ ((p3 ∧ ((p4 → ((False → ((p4 ∨ p3) → p4)) ∨ False)) → p2)) ∨ True)) ∧ (p2 ∧ ((p3 ∨ p5) ∨ p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51168162382142306131065015897 : (((((p3 ∧ ((((p2 → p5) → p1) → (p4 ∨ p1)) ∧ (p2 → False))) ∧ False) ∨ (True ∧ False)) ∨ (p2 → ((False ∧ p1) → (False ∧ True)))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37257164549259473583298367834 : ((((p2 ∧ (((((p4 ∨ (p2 ∨ p1)) ∨ p3) → p2) ∧ True) ∧ ((p4 ∧ p3) ∧ (((p3 ∨ (True ∧ False)) ∧ False) ∨ p2)))) ∧ p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



