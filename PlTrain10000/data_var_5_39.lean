variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317855973088895673536073285925 : (p4 ∨ (((p1 → p3) ∧ (((((((((p2 ∧ False) → False) → p4) ∨ True) ∧ ((False → p2) → False)) ∨ (p1 → p5)) → p3) ∧ p1) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177963437707803542193779566143 : ((((p2 → p4) ∨ (p4 ∧ (((p5 ∨ (p3 ∨ True)) → p3) → p3))) ∨ p3) ∨ (((False → (p1 → (p2 ∨ True))) → ((True → True) ∧ p5)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 → (p2 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179583178482376944117634718374 : ((p2 → (p2 → (p1 ∧ (((p2 ∨ p5) → ((p1 → p4) ∧ p4)) → False)))) ∨ (((p5 → False) → ((False ∧ p4) ∨ (p2 ∧ (p4 → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63314661661820126281184500634 : ((p5 ∧ ((p4 → False) ∧ ((p5 → ((((p2 ∧ (p3 ∨ True)) ∨ ((p5 ∧ p1) ∧ True)) ∨ p5) ∨ ((p2 ∧ (p1 ∨ p5)) ∧ p4))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57716282743161098229625508453 : ((((p5 ∧ p4) → True) → ((p1 ∧ (p1 ∧ ((p4 ∨ (p2 ∨ True)) → (((((False ∧ p3) → p1) ∨ (p3 ∧ True)) → p1) ∧ False)))) → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65633439842799204651140544668 : ((p4 ∨ ((((p2 → True) → (((p5 → ((True ∨ (p3 ∧ (True ∨ p2))) ∧ (p5 → (p5 ∧ p3)))) → p2) ∨ True)) ∨ (p1 → True)) ∨ p2)) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629615860198696884622630838576 : (((((((False ∧ p3) → ((((True ∧ p4) ∨ p3) ∨ True) ∨ (p4 → ((p1 → p5) ∧ (p3 ∨ True))))) ∨ ((p5 ∧ p4) → p5)) ∨ True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133917114117707457974375744735 : (((p4 ∨ ((((p1 ∧ (p3 ∨ p2)) ∨ p5) ∧ ((p5 ∨ (((p2 ∨ p5) ∧ (False ∧ p5)) ∨ p5)) → p2)) ∧ p4)) ∧ p4) ∨ (True ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352156272580189898833769621934 : (p4 → ((False ∨ (((p4 ∧ p2) ∧ p5) ∨ p5)) → (((((p3 ∨ p2) ∨ ((p1 ∧ (False → False)) ∨ p1)) ∧ False) ∨ (p5 ∨ (p4 → p3))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_826955148901117054323158024847 : ((((True ∧ (((p5 ∨ p4) → (((p5 ∨ p2) ∨ ((p2 → p5) ∨ ((p1 ∧ ((False → p1) ∧ p3)) ∨ True))) ∨ True)) → (False ∧ True))) ∧ True) → False) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∨ p4) → (((p5 ∨ p2) ∨ ((p2 → p5) ∨ ((p1 ∧ ((False → p1) ∧ p3)) ∨ True))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
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
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h6
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39781634781628450937845276133 : (((True → (p5 ∨ (((p3 ∨ p4) ∨ p5) → ((False ∨ ((p4 ∧ False) ∨ (p1 ∨ True))) → (p3 ∨ ((p2 ∨ p3) ∨ (p1 ∨ p3))))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300427857360507380549703129521 : (False ∨ ((((False ∧ (p2 ∧ p3)) ∨ (True ∧ (((False ∨ (p4 ∨ (p5 → (False → p5)))) ∧ (p3 ∧ p5)) → p3))) ∨ p2) → (p3 ∨ (p5 ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
theorem thm_5_vars_310388424022861373460868094320 : (p2 ∨ ((((True → (p3 ∧ (p2 ∧ True))) → p2) → p2) ∨ (((p4 → p3) ∨ (((p1 ∨ (False → False)) ∧ False) ∨ (p4 → (p4 ∨ p1)))) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48177836902966770498896262726 : ((((p5 → p5) ∧ (((False ∨ ((True → p1) → (True → (p3 → p5)))) ∧ ((p5 ∨ False) → p4)) ∨ ((p3 → p1) ∨ p3))) → (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225042130329169399493397593812 : (((False ∧ p4) ∧ p3) ∨ (p4 → ((p4 ∧ ((False ∧ ((True ∧ ((((((True ∧ p1) → p5) ∨ p1) ∧ False) → p4) → p3)) → p1)) ∧ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66361197306361043231680664466 : ((p5 ∨ (False ∨ (((((p4 ∧ (False ∨ (p4 ∨ p4))) ∧ False) → p2) → p3) ∨ ((True ∨ ((True ∧ (True ∨ (p4 ∨ False))) ∨ False)) ∨ p1)))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871041182217627098228511808806 : ((((p1 ∨ (((p3 ∨ p5) ∧ ((p2 ∧ ((True → (p3 ∧ p2)) ∨ ((False → (p3 ∧ (p5 ∧ p4))) ∨ (p3 ∧ p1)))) → p5)) ∨ True)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (((p3 ∨ p5) ∧ ((p2 ∧ ((True → (p3 ∧ p2)) ∨ ((False → (p3 ∧ (p5 ∧ p4))) ∨ (p3 ∧ p1)))) → p5)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666824292176185990853261468073 : ((((((((True ∧ p3) → p2) → p3) → (False ∨ p2)) → (p4 ∧ (((((p4 ∨ p1) ∧ p1) ∧ p5) ∨ p2) → p3))) ∧ ((True ∨ True) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39687644285077087620786903053 : (((p4 ∨ ((((p2 ∧ (p2 → (True ∨ p1))) → True) → p4) ∧ ((p1 ∧ (p3 ∨ ((p1 ∧ (p4 → (p2 ∧ p1))) ∨ True))) ∨ p1))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111006464871625498981889276544 : ((((((p2 ∨ ((p2 → p1) ∨ (p1 → ((False ∨ (p2 ∨ p2)) ∨ (p4 → p4))))) ∧ p4) ∨ p5) ∨ ((True ∧ p3) → p4)) ∧ False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184509014500397190465571383303 : ((((p3 → p2) → (p2 → (p2 → (p4 → False)))) ∨ (p4 → False)) ∨ ((p1 → p4) ∨ ((p4 ∧ ((((p5 ∨ True) ∧ p2) → p5) ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255665587241259921931455640830 : ((p5 ∧ p5) → ((((p5 → (p3 ∨ (((((False ∧ (p2 ∧ p4)) ∧ p2) ∧ p3) → (True → p4)) → (p3 ∧ (p1 → p1))))) ∧ p1) ∨ True) ∨ p5)) := by
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
theorem thm_5_vars_686396131741966151581298823124 : ((((((p4 → (p3 ∨ p4)) ∨ True) ∨ (p2 ∨ ((p5 ∨ ((False ∨ (p2 ∧ False)) → p4)) ∧ p2))) → (((p4 → (p4 ∧ p2)) ∨ p3) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111997609176607096089227436743 : (((((False ∨ (True ∧ p5)) ∧ p4) ∨ ((True → ((p4 ∨ ((p5 ∨ ((False ∧ (True → p5)) → p1)) ∧ True)) ∨ p5)) ∧ True)) ∨ p3) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_829197706896884575435364368826 : ((((False ∨ ((((False → (p2 ∨ True)) ∧ ((p4 ∧ p2) ∨ p3)) → False) ∧ ((p4 → p2) ∨ (p4 → ((p3 ∧ p4) → (p1 ∧ p2)))))) ∧ p3) → False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : ((False → (p2 ∨ True)) ∧ ((p4 ∧ p2) ∨ p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h9
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : ((False → (p2 ∨ True)) ∧ ((p4 ∧ p2) ∨ p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h13
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69234550084672995010363544260 : ((p5 → (((True ∨ (p3 ∧ p1)) → p3) → ((p5 ∨ ((False ∧ p4) → (True ∨ (p1 → ((False ∧ (False ∧ True)) ∧ (False ∧ p5)))))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234052393818961714187072656102 : ((p5 ∨ (p4 → True)) → (((p2 → (((True → p4) → p2) → False)) ∧ (True ∨ p5)) ∨ ((p4 ∨ (True ∨ ((True ∧ False) ∧ (p2 ∧ True)))) ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731575624866428614986578706807 : ((((False → (p5 → True)) → (((((p4 → p5) → (((p1 → p4) ∧ (False → True)) ∨ True)) → (p4 ∧ p4)) ∨ p4) → (p2 ∨ (True ∧ p4)))) ∨ p5) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 → p5) → (((p1 → p4) ∧ (False → True)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589445018607991605355070371352 : (((((((p5 ∨ p3) ∨ (True ∨ (((p4 ∨ p3) → p5) ∧ (((p4 ∧ p1) ∧ (False → p2)) → (p3 → (p5 ∧ p1)))))) ∨ p3) → p5) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55625583875674477253290158159 : (((p4 → (p2 → ((False ∧ p3) ∧ False))) → ((p1 ∧ (p5 ∨ p4)) → ((((False ∧ (True ∨ p4)) → (p3 → (p2 ∨ True))) → False) → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ (True ∨ p4)) → (p3 → (p2 ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h7
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((False ∧ (True ∨ p4)) → (p3 → (p2 ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h14
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164580718039314007546430246785 : ((((p4 → (p2 ∧ p2)) → (p3 ∨ ((p1 → ((p2 ∧ p3) ∧ (p1 ∧ p3))) → p1))) ∧ p3) ∨ (p2 ∨ ((False ∨ (p1 → p5)) → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_244414741833471299716315025042 : ((False ∧ p1) ∨ (False ∨ (p4 → (((True ∧ (p5 ∧ p4)) ∨ (((p3 → (False ∨ p4)) ∧ p3) → (p5 ∧ p1))) ∨ ((p3 ∨ (False → p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_39442936962366440556932673165 : (((p5 ∧ (((False ∨ False) ∧ ((False → (p4 ∧ ((((p4 ∨ p1) ∨ (p2 ∨ p4)) → (p2 → False)) ∧ p1))) ∧ p5)) ∧ (p2 → p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218886547747891335393585035658 : ((p2 ∧ (p5 → (p1 → p1))) → (p1 → ((((True → (p5 → (p2 → ((p3 ∨ (True ∧ p4)) ∧ (p5 ∧ p2))))) ∨ True) → False) ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190289835329828517683626222789 : (((((((True ∧ p2) ∨ p2) ∨ True) → p3) → p5) ∨ p1) ∨ ((p5 ∧ (p4 ∨ (p4 ∨ p3))) → (p5 → ((p2 ∨ (p5 ∨ p4)) ∨ (p1 → p1))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152580513688410675521774616698 : (((p4 → (p3 ∧ p1)) → ((((p4 → False) ∧ p1) ∧ (((p3 → (False ∨ True)) → p4) → (p1 → p1))) ∧ p1)) → ((True → p5) → (p4 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974555816402177391118161984006 : ((((p1 → p1) → (((False → ((p4 ∨ p5) → (p5 ∨ p5))) → (False → (((False → ((p4 ∧ False) ∨ (p2 → True))) → p4) → False))) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75083847613958585150578158454 : (((True → (((p4 ∧ ((p3 ∨ ((p5 ∧ (((p5 ∧ p1) ∨ False) → p1)) → p1)) ∨ (p1 → ((p4 → p2) → p1)))) ∨ p2) ∧ p5)) ∨ p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325109533399835391710782666859 : (p5 ∨ ((p4 → p1) → ((p1 ∧ ((p5 → (False ∧ p2)) ∧ (True → (((((p5 ∨ p1) ∧ p2) ∨ (p2 ∨ p4)) ∨ (p4 → True)) → p5)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((((p5 ∨ p1) ∧ p2) ∨ (p2 ∨ p4)) ∨ (p4 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h12 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h13 := h5 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341992353205820756683235039026 : (p2 → ((((((False ∧ p1) ∨ (p3 ∨ True)) → p5) → p2) ∧ ((((p1 → True) → p2) → p5) → ((p3 ∧ p3) ∨ False))) ∨ ((p2 ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124195771744317577348607997903 : (((p2 ∧ ((p4 ∨ (p3 → (False → (p4 ∧ p1)))) ∨ p1)) ∨ (True ∨ ((p4 → (p1 ∨ p5)) → (True ∧ (p2 ∨ (p3 ∨ True)))))) → (p3 ∨ True)) := by
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
theorem thm_5_vars_46810703881827161832546690055 : ((((((p4 ∧ ((False → False) ∧ (False ∨ (p4 → p4)))) ∨ (((p2 → ((True ∧ p3) ∧ False)) → p3) ∨ p2)) ∨ p3) ∧ p1) ∨ (p1 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618907091065406164602189812259 : (((((p3 → (True ∧ p3)) ∧ ((p5 → ((((p1 → p1) ∨ True) → p1) → ((p2 → (p3 → ((p3 ∨ p1) → True))) → p2))) ∧ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_1621936812053059882025423141 : (((p5 ∨ (((p3 → (p5 → p2)) ∨ ((p4 ∨ p1) ∨ False)) ∧ ((False ∨ True) → p5))) ∧ ((p1 ∧ (p3 ∨ p4)) ∧ p1)) → (p5 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h3.left
          let h25 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h24.left
          let h27 := h24.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h3.left
          let h32 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h31.left
          let h34 := h31.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
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
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338006171101360738207673544293 : (p1 → (((False ∨ ((p4 → p1) ∨ (True ∧ p4))) ∧ (p1 ∨ p1)) ∧ ((((((p3 ∨ (True → p1)) ∧ p1) → (True ∧ p4)) ∧ p5) ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251296171440163989298741613451 : ((p2 → p3) ∨ (((p5 ∨ True) ∧ (((p5 ∨ p4) ∨ (((p2 → p4) ∧ p1) ∨ (True ∧ (True → ((p1 ∧ p5) → (p1 → p4)))))) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69181207408435784202258305278 : ((p5 → ((((p5 ∧ True) ∧ True) → ((p4 ∨ ((p3 ∧ (p3 ∧ False)) ∧ p3)) ∨ p4)) ∨ (((True ∨ ((p2 ∧ True) ∨ p2)) ∨ p1) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_248865902608445045667431694104 : ((p3 ∨ p5) ∨ ((((((p5 ∧ False) → (p4 → (p3 ∨ (p4 ∧ p3)))) ∧ False) ∨ True) ∧ (p5 ∨ (((p1 ∨ p5) → p1) ∧ (p1 → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47974632009280800668334074144 : ((((((p2 → (True → p4)) → p3) → ((p1 ∧ False) ∨ (((p1 ∨ True) ∧ p2) ∧ p4))) ∨ (p3 ∧ ((p3 ∧ p5) ∨ p1))) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204207452853242081234756867004 : (((((p3 ∨ p5) → p4) → p5) ∧ p2) ∨ (((p5 ∨ (p5 → p4)) → ((p5 ∨ ((p4 ∧ (False ∧ (False ∧ p3))) → p4)) ∨ (p1 ∨ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41020059563734318181199128862 : ((((((((p2 ∨ True) → ((p4 ∨ (p4 ∧ (False ∨ p1))) → False)) ∧ (True ∧ p2)) → ((p3 ∧ False) ∨ p2)) → p2) → (p5 → p4)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685000195647366262181240313815 : ((((p4 ∧ (True ∧ (p1 ∨ ((((p1 ∨ p5) ∧ p3) ∨ (p3 ∧ ((True ∨ True) ∧ p2))) ∧ True)))) ∨ (True ∨ (False ∧ (p3 ∨ (p2 ∧ p5))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_178370206737744380647117234482 : ((((True ∨ (p4 ∧ (((p5 ∨ True) ∧ p1) ∨ p1))) ∧ p2) → (True → p5)) ∨ ((((p4 → (True → p1)) → p5) ∨ (p1 → (False ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_130429732468146671377838543772 : ((((p3 ∨ (((p4 → ((p5 ∧ True) ∨ p4)) ∨ (False ∧ (p4 ∧ p2))) → p3)) ∧ (p3 ∧ p5)) ∨ ((p3 ∧ p4) → p3)) ∧ ((p2 ∧ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58014218995673150224285450046 : (((True ∧ p1) ∧ ((p4 ∧ (p5 ∧ ((((True ∧ p3) ∧ p5) ∧ p5) ∨ p5))) ∧ ((p3 → (p3 → (p3 → (p3 ∧ p4)))) ∧ (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313481977015262975441796755262 : (p3 ∨ ((((p3 ∨ p5) → (((p2 ∧ (((False ∧ ((p1 ∧ (p4 → p3)) ∧ False)) → True) → p1)) ∧ (p4 → (True ∧ p4))) ∨ True)) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p5) → (((p2 ∧ (((False ∧ ((p1 ∧ (p4 → p3)) ∧ False)) → True) → p1)) ∧ (p4 → (True ∧ p4))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200840808739416123259224271035 : ((True ∨ ((((p1 ∧ p4) → p5) ∨ True) → p1)) → (p3 → (p5 ∨ (((p3 → True) ∨ p5) → ((p5 ∧ (p5 → p2)) ∨ (p3 ∧ (p5 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217274456055834414618997319499 : (((p2 ∧ (True → p3)) ∨ p3) → ((p2 → p2) → (((((p2 → p4) → p1) ∧ (p1 ∨ p2)) ∨ True) ∨ (((False → (p1 ∧ p3)) ∨ p5) ∧ p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328621594014646436124643613297 : (True → (((p3 ∨ p3) ∨ (((p3 ∧ False) → False) → ((p1 ∨ (False ∨ p4)) → p5))) ∨ (True ∨ ((((p5 ∧ p4) ∨ p5) ∧ True) ∧ (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137896236209730961504617326165 : ((p4 ∨ ((p3 ∧ (((p2 ∧ (((p5 ∧ p2) ∨ p2) ∧ ((p2 ∧ p4) → (p1 ∧ p2)))) ∨ p5) ∧ True)) ∨ (False ∧ True))) ∨ (p4 → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207602380554910227487107241108 : (((((True → p3) ∨ p2) → p2) → p2) → (p3 → (True → (((((p4 ∨ p2) → ((True → p4) ∧ True)) ∨ ((False ∨ p2) → p3)) ∨ p2) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148611547482739478595784895227 : ((((p3 ∧ (((p1 ∧ (p5 ∧ p3)) ∨ p1) → p3)) ∨ False) → ((p3 → p1) → ((p5 → (p1 → p4)) ∨ p4))) ∨ (True ∨ (p2 ∨ (False ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147367025089158526025021716985 : (((((False → False) → ((False → (p1 ∧ ((p4 ∧ False) ∧ True))) ∧ False)) ∧ (p1 → ((False → p4) ∨ p3))) ∨ p5) ∨ ((p2 ∨ p2) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64118877707980995141662998844 : ((False ∨ ((p1 → (((p4 ∨ p3) ∨ p1) → p2)) ∨ ((p1 ∨ True) → (((p3 ∨ ((p2 ∧ p1) ∨ p2)) ∧ p5) ∨ (False ∨ (False ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246465558930798558817734091675 : ((p5 ∧ False) ∨ ((True ∨ (p5 → p1)) ∧ (p5 → ((((False → p3) ∧ (p1 → ((p4 ∧ (p3 ∧ p4)) ∧ ((p1 ∨ False) ∧ p5)))) ∨ True) ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54924207506023423605284420215 : (((((p4 → p1) ∨ (p4 ∨ p4)) → True) ∧ (((True ∧ ((p1 ∧ p5) → False)) ∨ p2) ∨ ((p3 → p4) ∧ (((p5 → p2) ∨ p3) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260055945473443268439495295311 : ((p2 → False) → ((True ∧ (False ∨ (((p3 ∨ p5) ∧ ((((p2 ∨ True) ∨ (p5 ∧ p4)) ∨ (p3 → False)) ∧ p2)) ∨ p2))) → ((p2 → p1) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
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
        let h12 := h10.left
        let h13 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h17 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h13
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h18 := h1 h17
              -- False on the left can always be used.
              apply False.elim h18
            case inr h19 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h20 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h13
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h21 := h1 h20
              -- False on the left can always be used.
              apply False.elim h21
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h25 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h13
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h26 := h1 h25
            -- False on the left can always be used.
            apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h28 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h29 := h1 h28
          -- False on the left can always be used.
          apply False.elim h29
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h10.left
        let h32 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h35 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h36 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h32
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h37 := h1 h36
              -- False on the left can always be used.
              apply False.elim h37
            case inr h38 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h39 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h32
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h40 := h1 h39
              -- False on the left can always be used.
              apply False.elim h40
          case inr h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h44 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h32
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h45 := h1 h44
            -- False on the left can always be used.
            apply False.elim h45
        case inr h46 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h47 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h48 := h1 h47
          -- False on the left can always be used.
          apply False.elim h48
    case inr h49 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h50 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h49
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h51 := h1 h50
      -- False on the left can always be used.
      apply False.elim h51
  -- Conjunctions on the left can always be decomposed.
  let h52 := h2.left
  let h53 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h53
  case inl h54 =>
    -- False on the left can always be used.
    apply False.elim h54
  case inr h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- Disjunctions on the left can always be decomposed.
      cases h57
      case inl h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h58.left
        let h61 := h58.right
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h62 =>
          -- Disjunctions on the left can always be decomposed.
          cases h62
          case inl h63 =>
            -- Disjunctions on the left can always be decomposed.
            cases h63
            case inl h64 =>
              -- One of the premise coincides with the conclusion.
              exact h59
            case inr h65 =>
              -- One of the premise coincides with the conclusion.
              exact h59
          case inr h66 =>
            -- Conjunctions on the left can always be decomposed.
            let h67 := h66.left
            let h68 := h66.right
            -- One of the premise coincides with the conclusion.
            exact h59
        case inr h69 =>
          -- One of the premise coincides with the conclusion.
          exact h59
      case inr h70 =>
        -- Conjunctions on the left can always be decomposed.
        let h71 := h58.left
        let h72 := h58.right
        -- Disjunctions on the left can always be decomposed.
        cases h71
        case inl h73 =>
          -- Disjunctions on the left can always be decomposed.
          cases h73
          case inl h74 =>
            -- Disjunctions on the left can always be decomposed.
            cases h74
            case inl h75 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h76 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h72
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h77 := h1 h76
              -- False on the left can always be used.
              apply False.elim h77
            case inr h78 =>
              -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
              have h79 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h72
              -- We have shown the premise of h1, we can now drive its conclusion.
              let h80 := h1 h79
              -- False on the left can always be used.
              apply False.elim h80
          case inr h81 =>
            -- Conjunctions on the left can always be decomposed.
            let h82 := h81.left
            let h83 := h81.right
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h84 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h72
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h85 := h1 h84
            -- False on the left can always be used.
            apply False.elim h85
        case inr h86 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h87 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h72
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h88 := h1 h87
          -- False on the left can always be used.
          apply False.elim h88
    case inr h89 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h90 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h89
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h91 := h1 h90
      -- False on the left can always be used.
      apply False.elim h91



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865168972294593159896319403073 : ((((((p2 ∨ ((p4 ∨ p3) ∨ False)) ∧ p2) → ((p3 ∧ (True ∨ False)) ∨ (((p4 → (p3 ∨ (True ∨ p3))) ∧ (True → p3)) ∨ p2))) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ ((p4 ∨ p3) ∨ False)) ∧ p2) → ((p3 ∧ (True ∨ False)) ∨ (((p4 → (p3 ∨ (True ∨ p3))) ∧ (True → p3)) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178665247720807444450206594690 : ((((p3 ∨ False) ∨ (True ∨ p2)) ∧ ((p2 → ((p2 ∧ p4) ∨ False)) ∨ p5)) ∨ (p3 ∨ (True ∧ ((True ∨ p3) ∨ ((p3 ∧ (p4 → p5)) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263679256253500588987745382937 : (True ∧ (((((p4 ∨ True) → p5) ∨ (p4 ∨ (((p3 ∧ (p3 ∨ p4)) → False) → (p2 → False)))) ∧ p5) ∨ (p1 ∨ (p3 → (p5 → (p5 ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348847831513463954298720147322 : (p3 → (p2 ∨ (((((((p3 ∧ False) → p2) ∧ (p3 ∨ p4)) ∨ (p5 ∨ ((False ∧ ((p4 ∨ p3) ∨ p5)) ∧ p3))) → (p1 ∧ False)) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234117273894416877605359057971 : ((True → (p1 ∨ p3)) → ((p1 ∨ ((p2 → ((((p3 → False) → ((p3 → True) ∧ False)) ∨ True) ∧ p2)) → (p4 ∧ ((p5 ∨ p2) ∧ p1)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → ((((p3 → False) → ((p3 → True) ∧ False)) ∨ True) ∧ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595369692989162782879306875316 : (((((p3 ∧ (((False ∨ (p1 ∧ (p3 → (p1 → True)))) ∨ p1) ∨ p4)) ∧ (p5 → ((False ∨ (p5 ∨ True)) ∨ ((True ∧ p2) → True)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116347609789817668406114795410 : ((((True ∨ p1) ∨ p3) → ((p1 ∨ (((p3 → p4) ∧ p3) → ((((p1 ∧ False) ∨ p1) ∨ (p1 ∧ (False ∧ p2))) ∨ p3))) ∨ False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639376950609225149771983775606 : (((((p1 ∧ (True ∧ (p2 ∨ p2))) → ((p1 ∧ (p4 ∧ ((p3 ∧ (((False ∧ p4) ∨ p4) ∧ (p3 ∨ True))) ∧ p2))) ∨ (p5 → p1))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139718728340828029600594077883 : ((((p5 ∧ p1) → ((((p4 ∧ ((True → p4) ∧ (p1 ∨ p5))) ∧ (p3 → p2)) → p3) → ((p2 ∧ p3) ∧ p5))) → False) → (p2 → (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338164249465307855789051403132 : (p1 → ((((p4 ∨ (True ∨ p4)) ∧ p3) → (p5 ∧ True)) → (((p5 → (((p1 → p4) ∨ (p1 ∨ p4)) ∨ p3)) ∨ (p3 ∧ (p4 ∨ p3))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52535231531034113282475500863 : ((((False ∧ (((p3 → ((False ∨ p2) ∧ (p2 ∨ p3))) → p3) ∧ p3)) ∨ p1) ∨ (((p1 → ((p3 → p1) ∧ p3)) ∨ (False ∨ True)) ∨ p2)) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178072363965945267081585891002 : ((((p1 ∨ ((((True → False) ∨ (p1 → p2)) ∧ p2) ∨ p4)) ∨ p5) → p1) ∨ ((((p4 ∨ (p1 → False)) ∧ True) ∨ ((p2 ∨ True) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53676981742897538968017677616 : (((True ∧ (((True ∨ ((p3 ∧ p1) ∧ p2)) ∧ p2) ∧ True)) ∧ ((p1 ∨ ((p4 → (p3 ∨ (p4 ∧ p2))) ∨ (p3 ∧ (p2 → p2)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148037159077066682894302603002 : ((((p4 ∧ True) ∨ (((False ∨ (((((p1 → False) ∨ p2) ∧ True) ∨ p5) → p2)) ∨ True) ∧ False)) ∨ (True → p5)) ∨ (p5 ∨ ((p4 ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135269964013169882352031800500 : (((p1 ∨ ((((p4 → p3) → (p1 ∨ ((p2 → (False ∨ (p5 ∨ (p1 ∨ False)))) ∧ True))) → True) ∨ True)) → (False ∧ p2)) ∨ ((p2 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134279542424732481235553922086 : ((((p5 → False) ∧ ((p4 → (p2 → (((p1 ∨ (p2 ∨ (p2 ∨ False))) ∨ (p1 ∨ p4)) ∧ True))) → (True ∧ p4))) ∨ False) ∨ ((p2 ∨ True) ∧ True)) := by
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
theorem thm_5_vars_299151084086151984208418985074 : (False ∨ (((p3 ∧ ((((p5 ∧ (False ∨ (((False ∨ (p2 ∧ p4)) → p3) ∨ p5))) ∨ p3) ∨ (True → (p2 ∧ False))) ∨ (p4 → p5))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171019241286686265516146933088 : ((p3 ∨ (p5 ∨ (p4 → (((False → p5) ∨ (p2 ∧ ((p5 ∨ True) ∨ p1))) ∨ p5)))) ∧ (p3 ∨ ((p2 ∨ True) → (p2 → (p1 ∨ (False ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78237986996198702540217947116 : (((p3 → ((((p5 ∨ p5) ∨ (p2 ∨ True)) → p2) ∨ ((p3 ∧ (p5 ∨ ((((p2 → p2) → p1) ∨ p1) ∨ (False → p2)))) ∨ p2))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((((p5 ∨ p5) ∨ (p2 ∨ True)) → p2) ∨ ((p3 ∧ (p5 ∨ ((((p2 → p2) → p1) ∨ p1) ∨ (False → p2)))) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118141088226552354250508206346 : ((False ∨ (((((p3 ∧ (True → (p2 ∨ p5))) → False) ∧ p3) ∧ ((True ∨ p5) ∧ False)) ∨ (((p2 ∧ (True ∨ p3)) ∧ p4) → True))) ∨ (True ∧ p3)) := by
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
theorem thm_5_vars_40482245288727195755262975562 : (((((p2 ∧ p2) ∨ (((False → (((p1 → p4) ∧ p1) ∧ ((p2 ∧ ((p3 ∧ p3) ∨ p5)) ∨ (True ∧ p4)))) → p5) ∧ p5)) ∨ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336346014848140344658610416860 : (p1 → (((p4 ∨ p2) ∧ (((p5 → p2) ∨ ((True ∨ p5) ∨ True)) → ((False ∧ p2) ∨ (True ∨ ((p5 → ((p4 ∧ p1) ∨ False)) ∨ False))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617709384485960840227704951919 : ((((((p4 ∨ p4) ∧ ((False ∧ p3) ∨ p4)) ∨ (p5 → (True → ((p3 → ((p3 ∧ (p5 → (p3 ∧ p4))) ∨ p3)) ∧ (p5 ∨ p1))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_310608828157554939424314447640 : (p2 ∨ (((p5 ∨ (p4 ∧ p5)) ∧ p3) ∨ (((((p5 ∧ p4) → True) ∨ (p3 → p2)) → p1) ∨ (True ∧ (p5 → ((p1 → p5) ∨ (False ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134107888248962766323063231941 : (((((True ∧ (((p5 ∧ p1) ∧ (p1 → p3)) ∧ (p1 → (p4 ∨ (p2 ∧ p5))))) ∨ (False ∨ True)) ∧ (True → False)) ∨ True) ∨ ((p5 ∨ p1) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134148790079477509674844416864 : (((((p1 ∧ ((p4 → p4) → (p2 → ((True → ((p2 ∧ p1) ∨ True)) → False)))) ∧ p2) ∨ ((p4 ∧ False) ∧ p2)) ∨ p3) ∨ (p2 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67524830576518903907867839725 : ((p1 → ((((False ∧ p5) ∧ p4) → p5) ∧ (p4 ∧ (p1 ∧ ((((True ∧ p2) ∨ p4) ∧ (False ∨ p2)) ∧ ((p5 ∨ p2) ∨ (p4 ∧ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306455218203388975062570868763 : (p1 ∨ ((p3 ∨ p2) ∨ (((False → ((p1 → p1) ∧ p2)) → ((p3 → (p3 → ((True ∨ p3) ∨ p5))) ∧ False)) → (p3 ∧ ((False ∨ False) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p1 → p1) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False → ((p1 → p1) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259941768736459651374345998463 : ((p1 → p5) → (((p3 ∧ (((p1 ∨ False) ∧ (p3 → p5)) ∨ p4)) ∨ True) → ((((((p3 → p5) ∨ (p2 ∧ p4)) → p2) → p3) ∨ True) ∨ p4))) := by
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
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346313937178805109261314473911 : (p3 → ((((((((((p1 ∨ (p3 ∧ True)) → p3) ∨ p2) ∧ p3) → (p2 ∧ p5)) ∨ False) ∨ p4) ∨ (p2 → p5)) ∧ (p4 ∨ True)) ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68787020039256724780865672410 : ((p4 → (((p3 ∨ p1) → (p1 ∨ ((False ∨ p2) → p3))) → (((p5 ∧ (p5 → p3)) ∧ ((True → p2) ∧ (p4 → False))) → (p2 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149406984662959417817508325470 : ((True ∧ ((True ∧ (((p1 → p4) ∧ (((False ∨ ((p1 → True) ∧ p3)) ∨ p2) → False)) ∧ p2)) ∨ (p1 ∧ p1))) ∨ ((p5 ∧ p1) → (p5 → p5))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138459130093995279919495150446 : ((p5 → (p1 ∨ ((p5 → (((p1 ∧ ((p3 ∨ True) ∨ (p4 → (p5 ∨ ((False ∨ p3) → p2))))) ∨ p2) → p4)) → p1))) ∨ ((p1 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



