variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349762024697504515104560964228 : (p4 → ((((p5 ∨ (p1 → p3)) → p1) → ((p3 ∨ ((p4 → True) → (p3 → p1))) ∨ (p1 ∧ (True → (p4 ∨ ((p4 ∨ p3) ∨ p4)))))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ (p1 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51129009312259460999179692251 : ((((p3 ∧ ((((p4 → p3) → p5) ∧ (p4 ∧ (((p5 ∧ False) ∨ p3) ∧ p2))) → False)) ∨ False) ∨ (p1 ∧ (((p3 → p4) ∧ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262354072708584436443622027493 : (True ∧ ((((p5 → p4) ∨ p2) ∧ (p3 ∧ (((((False → (p4 → p5)) ∧ (True ∨ (p1 → p4))) ∧ (p2 → (p3 ∨ p5))) ∧ p3) ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149604366858079153927431202865 : ((p3 ∧ ((p1 → ((p1 ∧ False) ∨ p5)) ∧ ((p1 ∧ False) ∧ ((p4 ∨ (((p5 ∧ p5) ∨ p2) ∧ True)) → p2)))) ∨ ((p2 ∧ p4) → (p3 ∨ p4))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111828816557506326196261930902 : ((((p2 ∧ (p2 ∨ (p3 ∧ ((False ∧ ((p2 → p2) → ((p4 ∧ p1) ∨ p3))) ∨ (p2 → p5))))) ∧ (p1 → (p3 ∨ p2))) ∨ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57988806552484369371909198932 : (((p4 → (p5 → p1)) → ((((p4 → False) → ((((p5 → (p1 → (p3 ∨ p2))) ∨ p2) → p5) ∧ (False → False))) ∨ (p4 ∧ False)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45838578255104951819343596469 : (((p2 → (((p2 → p3) → (True ∧ p2)) ∨ (((p5 ∨ True) ∨ ((False → ((p3 → (p2 ∧ p5)) ∨ True)) ∧ (p1 ∨ False))) → p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147683586607967788038172168334 : (((((((p1 ∨ False) → p3) ∨ True) → (p1 ∧ (p3 → (False ∧ (True → p5))))) ∨ (p1 ∧ (p3 ∧ p5))) → p4) ∨ (p5 → ((p3 ∨ p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350977934328817176463725996944 : (p4 → (((p3 ∧ (p5 → p5)) → (((p3 ∨ p1) → ((False ∨ p5) ∨ (False ∨ p4))) ∧ ((p1 ∨ True) ∧ ((p2 ∨ p4) → p4)))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788550178582242997329757500467 : (((p5 ∨ ((p3 → (((False ∨ p2) ∧ ((True → p3) ∨ (p4 ∧ p5))) → ((((p4 ∨ p5) ∧ True) ∨ ((p3 ∨ p5) ∧ p2)) → p5))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_49444546969594816997627477801 : ((((((((p2 ∨ p1) → p2) ∨ False) ∧ (p3 ∨ p1)) → (p3 → (((p1 ∨ p3) → False) ∨ (False ∧ True)))) ∨ p1) → ((p1 → p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346798222648269395419109109399 : (p3 → ((p4 ∧ (p5 ∧ (((p4 → (True → False)) → p5) → ((p2 → ((False ∨ (p4 → p3)) → p3)) → p1)))) ∨ ((True ∨ (False ∧ p2)) → p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688838697668976341364810952530 : ((((((p4 → ((((p4 ∧ p2) ∨ ((p4 ∧ p5) ∧ False)) ∨ p3) ∨ p5)) ∨ False) ∧ p1) ∨ (p2 ∨ (True ∨ (p5 → ((False ∨ False) ∧ p5))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_642257301051744715564032819881 : ((((True ∧ (p3 → (p3 ∨ (((True ∨ p4) → (((p4 → ((True → p3) → p5)) ∨ (p2 ∧ p3)) ∧ p4)) ∧ (False → (p3 ∧ False)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798286178694051970214414582397 : (((p1 → ((True ∧ (((p5 → (((p2 ∨ False) ∧ True) ∧ (p1 ∧ p5))) ∨ (p4 → p1)) → p3)) → ((((p2 ∧ True) ∧ True) ∧ p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47594837049248984358589012395 : (((p3 → (((p4 ∨ ((p4 ∨ p1) ∨ ((p2 ∨ p1) ∧ (p3 → p2)))) ∧ ((p4 ∨ (p5 → (True ∧ True))) ∧ p4)) ∨ True)) ∨ (p4 ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719665911424396092078272433125 : ((((True → ((p4 ∧ p2) → p1)) ∨ (False ∨ ((p4 → (((p2 → True) ∧ ((False → p2) → False)) → ((p3 ∨ (False ∧ p5)) ∨ p5))) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165206853555155615140742991802 : (((((p4 ∧ p4) → ((p3 ∨ False) ∧ (p2 ∨ ((p5 → True) → p5)))) → p2) ∨ (True ∧ p3)) ∨ (True ∧ (p4 ∨ ((False → (p2 ∧ True)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_800683853011700077273550063675 : (((p2 → ((p5 ∧ ((False → (((((p5 → ((p3 ∨ (True → p4)) ∧ True)) → (p3 ∨ p1)) ∨ False) → False) → p1)) ∧ (p2 → p2))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197000212072933675556418732915 : (((((p1 ∧ True) ∧ p5) ∧ (p5 ∨ p5)) ∨ p5) ∨ (p5 → ((p2 ∧ ((p1 ∧ p1) ∨ True)) → ((p4 ∧ p3) → (((False ∧ p4) → p4) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105459715026570757107049690494 : (((((p1 ∧ ((p4 ∨ p4) ∧ p5)) ∨ ((True → p5) ∨ (False ∨ (True ∧ p1)))) ∨ (False ∨ p4)) ∨ (p2 → ((False ∨ p2) ∨ p1))) ∧ (True ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602228411581133504632703056693 : ((((p5 ∧ (p5 ∨ ((((p4 ∧ ((p4 → (p2 ∨ (((p5 → p3) ∧ p1) → p5))) ∧ (p4 → p3))) ∨ (p5 ∨ p1)) ∨ p1) ∧ p1))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150025786591151501251882020766 : ((p5 ∨ (((p4 ∧ True) → (p2 → p3)) → ((True → ((p1 ∧ p3) → ((True → (False ∧ p4)) ∧ p1))) ∨ p3))) ∨ (((False → False) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65687121838461619788708505390 : ((p4 ∨ (((p2 → False) ∨ ((p5 ∧ (p1 ∧ p1)) ∨ ((((p2 ∨ False) ∧ p1) ∧ (p3 ∧ ((True → p3) ∧ p4))) → (False → p3)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58718027091716804338368151786 : (((p3 → False) ∧ ((p5 ∨ p1) ∧ ((((((p3 → p1) ∧ False) ∧ False) ∧ (False ∨ (p5 → p1))) ∧ ((False → p5) ∧ (p2 ∧ p5))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147892522566075387915679379837 : (((((True ∧ (((p4 → True) ∨ True) ∧ (((p4 → (True ∨ p5)) ∨ True) → p1))) ∨ p5) ∨ p4) ∧ (False ∧ p2)) ∨ (((p3 ∨ True) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55576607512250990404364971189 : (((False ∨ (p1 → (p5 ∧ (p4 ∧ p5)))) → (((False ∨ ((False ∨ p2) ∧ p2)) ∨ (p3 ∨ (p5 → (p3 → p5)))) ∨ (p2 ∧ (p4 ∨ p4)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313008280115652812041683518460 : (p3 ∨ ((((((((p3 ∨ p3) → p3) ∨ True) ∧ ((p4 → p4) → True)) → p5) ∨ (((p2 ∧ p1) ∧ (p1 → p1)) ∨ (p2 → p4))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57813014629820960106837532593 : (((p3 ∧ (True ∧ p1)) → (((p2 ∨ ((p3 ∨ p5) → p5)) ∧ (False ∨ ((p2 ∨ p2) ∨ p5))) ∧ ((p5 → p1) ∧ (p5 → (True ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301825823482706345101847694949 : (False ∨ ((p2 ∨ p1) ∨ (((p3 → (True → ((p2 → p5) ∨ p1))) → p5) → ((p5 ∧ p1) ∨ (p3 → ((p2 ∨ (p5 ∧ (False → p1))) → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233407999275586596638141922550 : ((False ∨ (p1 ∨ p2)) → (((p4 → (p4 ∧ (((True ∨ (p5 → p2)) ∧ p5) ∨ (True → (p3 ∧ p4))))) → ((False ∧ False) ∨ p2)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709965246144515326980099926596 : ((((((False → (True → False)) → p1) ∧ p5) ∧ ((p2 → False) ∨ (p2 ∧ ((True ∨ (((p3 ∨ True) → True) ∨ p5)) → (p4 ∧ (p4 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657901981882710677293090845341 : ((((p1 ∧ (((p5 ∨ p3) → (p1 → ((((True → (False → (p1 ∨ (False ∧ p4)))) → p1) → p5) ∧ (p5 → p5)))) → False)) ∨ (p2 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_300864334471508212337760446502 : (False ∨ (((((((True → True) → (p3 ∨ p4)) ∧ (False ∨ p5)) → False) → p3) ∧ True) ∨ ((p1 ∨ False) → ((((p5 ∨ p2) → p5) ∨ p4) ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338554195515382906696841565180 : (p1 → ((p4 ∨ (False ∨ p2)) ∨ (True → (p3 ∨ (p4 ∨ (False → (p3 → ((((((p2 ∧ p3) → p2) → True) ∧ p1) ∧ (p5 ∧ False)) ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113443372705909300215593208672 : (((((p2 ∧ p4) ∨ ((((p3 → p2) → p2) ∨ p5) ∨ (True → (((True ∧ p2) ∨ p5) ∧ (p4 → True))))) ∨ p3) ∨ (p1 ∨ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694489945148177417094661332450 : ((((True ∧ ((False ∨ (((p4 ∨ (p2 ∧ True)) ∨ False) ∧ (p4 ∧ p1))) ∧ p4)) ∨ (p4 → ((p2 ∨ (p4 ∨ p4)) ∧ ((p4 ∨ p4) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233652197402156395613316400457 : ((p2 ∨ (p2 ∨ p5)) → (((((p4 ∨ ((p1 → p3) ∧ (p1 ∧ (True → p2)))) ∨ p2) → (((True ∨ False) ∨ p1) → p2)) ∨ p1) ∨ (True ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261193261653179351032390732709 : ((p4 → p5) → (((p1 ∨ (((((((False ∨ (p1 → (p2 → p1))) ∨ p3) ∧ p4) → (p3 ∧ False)) → p5) ∧ p4) → p2)) ∨ (p5 → True)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164795922003836028628450402577 : (((((p3 ∧ p3) ∧ p2) ∧ (((False → ((p5 ∨ (p3 ∧ p3)) ∨ p1)) → False) → p4)) ∨ False) ∨ ((True ∧ (((True ∨ p1) → False) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680517805466936004426589715264 : (((((True → (True ∧ ((p5 ∨ ((p3 ∧ True) → True)) ∨ p1))) ∨ (True → (p2 ∧ ((p1 ∨ p3) ∨ p3)))) → ((p3 → (p4 ∧ p4)) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_251024950582257195162782140580 : ((p1 → p5) ∨ ((p5 ∨ p4) ∨ ((True ∧ (p3 → True)) → ((((p1 ∧ p3) → ((p4 ∧ p5) → False)) ∨ p5) → ((True → (p3 ∧ p4)) → p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137279367923341526081660070119 : ((p2 ∧ ((((p5 → ((False → ((p5 ∨ (p1 ∧ p1)) → ((False ∧ p1) ∨ p1))) ∧ (False ∨ p4))) ∨ p1) ∧ p2) ∧ p4)) ∨ (p5 → (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158419643194714414946272578961 : (((p3 ∧ p4) ∨ (False ∧ ((True ∧ (p2 → (p1 ∧ (((p1 ∨ p2) ∨ True) ∧ (p2 ∨ False))))) ∨ p3))) ∨ ((False ∨ (True ∨ (p3 ∧ True))) ∨ p4)) := by
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
theorem thm_5_vars_137065228060863888818794018802 : (((p3 → p2) → ((((p1 → (p2 ∨ False)) ∧ p5) ∧ ((True ∨ (False ∨ p1)) ∨ False)) ∧ (True ∨ (p2 ∧ (p5 ∨ False))))) ∨ (p3 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56469489537895043671450981334 : ((((p2 ∨ False) → (p2 ∨ False)) → ((p1 ∧ (p3 → ((p4 → p1) ∨ p5))) ∨ ((p4 → ((False → p1) → p1)) → ((True ∨ p4) ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319177686567026157876889980684 : (p4 ∨ (((p4 ∨ False) ∧ ((((p3 ∧ (False ∨ True)) ∧ (False ∨ p4)) ∧ (p3 ∨ (p1 ∧ p2))) ∧ p3)) ∨ (True ∧ (False → ((p1 ∧ p5) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467179586110909232984413742262 : (((((True ∧ ((((p2 → False) → p4) ∧ p5) → (p2 ∨ (p1 → False)))) ∨ True) ∨ (p5 ∨ ((((p3 ∧ (True ∨ p2)) → True) → p3) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319154783686803106313835290123 : (p4 ∨ ((((((p1 ∧ (p4 ∨ ((p5 → False) ∨ (True → p4)))) → p1) → False) ∧ (False ∧ p1)) ∧ p3) ∨ (p1 → ((p3 → (p5 → p5)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310037562792977512068945761025 : (p2 ∨ (((p2 → p1) → ((p1 ∨ p4) ∨ ((True → (p4 ∨ (p5 → (p4 ∧ False)))) ∨ True))) ∨ (((False → True) ∨ p5) → ((p1 → True) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66249414908969708351673988565 : ((p5 ∨ (((False → (p1 ∧ p3)) ∨ p2) ∧ (False ∧ (((p1 ∧ ((((p4 ∨ (p3 → False)) → (False → True)) → p1) → True)) ∧ p4) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56624338663536471041836539708 : ((((p2 ∧ p2) ∧ p2) ∧ (((False ∨ (((p1 → p5) ∨ (p5 → (p4 ∨ (p3 ∧ False)))) → p2)) ∧ ((True ∧ (p1 ∨ p2)) ∨ p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310020611424189607911871971261 : (p2 ∨ (((False ∨ (((p4 ∧ (p5 ∧ True)) ∨ False) ∨ (((True → p5) ∨ p2) ∨ p2))) ∨ False) ∨ (p4 ∨ ((((p1 ∨ p4) → True) ∨ p2) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710322463748432828874537831490 : (((((((p5 → p1) ∧ True) ∧ p4) → p5) ∧ (((p1 → ((p2 ∧ p4) ∨ ((p1 ∧ (p4 ∨ False)) ∧ (False → (True → p4))))) → p4) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677662344873221673001694172613 : (((((((((p2 ∨ p2) ∧ (p4 ∨ (True ∨ p1))) ∨ (p5 ∧ p4)) ∧ p5) ∧ ((True → p5) ∨ p5)) → p4) ∨ ((True ∧ p2) → (False → p5))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157979625637662257384894388331 : (((((((p3 ∧ p4) ∧ p3) → p5) → p3) ∧ p5) → (p4 → (True ∧ (p3 → ((True → p3) → False))))) ∨ ((p1 → p1) ∨ (p4 → (p3 → True)))) := by
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
theorem thm_5_vars_178477844238153156062331044708 : (((((p3 ∧ (p3 → (p3 ∧ p5))) ∨ p4) → p1) ∨ ((p2 ∧ p2) ∨ False)) ∨ (((True ∧ p4) → True) → ((p5 ∨ (True → p1)) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_327706204981392740749669437175 : (True → ((((((((p5 ∧ (True ∨ p3)) ∧ (p5 ∧ (False → p4))) ∨ p3) ∧ False) ∨ (p4 → (p4 → p2))) ∨ p2) ∨ (True → True)) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606825563316117342754667828613 : (((((((p5 → (p4 ∨ p1)) ∨ ((p3 ∨ ((p4 ∨ p5) ∨ (True → ((False → p1) ∧ False)))) → p1)) ∧ ((p4 ∨ p5) → p5)) ∧ p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778267561460116098461839203231 : (((p1 ∨ (True ∧ ((((((p1 → ((p5 → (p2 ∧ True)) ∧ (p3 ∨ False))) ∨ p3) ∧ (p4 → (p2 ∧ p3))) ∨ p3) ∨ False) → (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659154942446585761985524288797 : ((((p3 → (((p1 → (p3 ∧ (p1 ∧ p2))) → (True → (p2 ∧ p2))) → (((p4 → False) ∧ p4) ∨ ((p5 ∨ p3) ∨ p5)))) ∨ (False → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_191329851539851854383643955257 : (((p3 ∧ False) ∨ (((p4 ∧ p5) ∨ (False ∧ p2)) ∨ p4)) ∨ (((p4 ∧ p5) ∨ (((p4 ∧ (p1 ∧ p4)) ∧ (True ∧ p2)) ∧ (False → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191176532416161606293881595117 : (((True → (p1 ∨ False)) ∨ ((p1 → (p3 ∧ p1)) → p4)) ∨ ((p5 ∨ ((p4 ∧ p5) → (p2 ∨ p4))) → (p1 ∨ (False → ((p2 ∨ p4) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350238555087559441837863172408 : (p4 → (((False → True) → ((p5 → (p1 ∧ p4)) → (p5 ∧ (((p3 ∨ (p5 ∨ p5)) → (False → (False ∨ ((p1 → p3) ∧ p3)))) ∨ False)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85342027141934064379586258636 : ((((False → ((True ∧ p2) ∧ (p2 → (True ∧ (p2 ∨ False))))) → p1) ∧ (((p3 ∨ (False → (p5 → (True → p5)))) → (p4 → p2)) → p3)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → ((True ∧ p2) ∧ (p2 → (True ∧ (p2 ∨ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147011344493983983869443725193 : ((((p5 ∨ (((p4 ∧ p3) ∧ ((p2 → ((p1 ∨ True) → (p2 ∧ p5))) ∧ p1)) ∨ p5)) ∨ (p4 ∧ p3)) ∧ False) ∨ ((p3 ∨ p1) → (p4 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113617067015036401717801722392 : (((True → (((((False → p5) ∨ (p4 → (p2 → ((p3 → p3) → (True → (p1 ∨ p5)))))) → p2) ∨ p2) ∨ p5)) ∨ (True ∨ p2)) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49929332899736108811346195548 : ((((True ∨ ((((p4 ∨ True) ∨ False) ∧ True) → ((p2 → (p2 ∧ p1)) ∨ ((False ∧ True) ∨ p4)))) → p3) ∧ (p2 ∧ (p5 → (p3 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137724705339150711340449540664 : ((p1 ∨ (False ∧ ((p2 ∨ (p1 ∧ (p4 ∨ ((p3 → False) ∨ (p5 ∧ (p3 → (False ∨ p1))))))) ∨ (p1 ∧ (p3 → False))))) ∨ (False ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41348163859493277304260435510 : ((((p2 ∧ ((((p4 → True) ∧ p5) ∨ ((True → p5) → (p5 ∧ (p5 → True)))) ∨ p4)) ∨ (True ∧ ((p5 ∧ (p5 ∧ p3)) ∨ True))) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136001602397680776391509193781 : (((False ∨ ((((p3 ∧ p2) ∨ p2) ∨ (True ∧ p1)) ∨ p1)) ∨ (p5 ∧ ((((p3 ∨ p5) → (True ∨ p2)) → False) → p4))) ∨ (p3 → (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304106175050694870204659135738 : (p1 ∨ ((p1 → (p4 ∨ (p3 → (p5 ∨ ((p5 ∨ p2) ∨ ((p5 ∨ (p1 ∧ ((p5 ∨ p4) ∨ (p5 → (p1 ∨ (p5 ∧ p2)))))) ∨ True)))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_704459758197324527211919191562 : ((((((p5 ∨ p5) ∨ p4) → ((p4 ∧ (p5 ∧ p5)) ∨ p5)) → (((p1 ∧ (p2 → (((p2 ∨ p1) ∨ False) ∨ p4))) ∨ p1) ∨ (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66285204914021323911908892546 : ((p5 ∨ ((p1 ∨ False) ∧ (p3 ∧ ((p2 ∧ ((((False ∨ p3) → p2) ∧ True) → ((p2 ∧ p5) → (((True → False) ∨ True) → p3)))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179428014550446055666688249982 : ((p4 ∨ ((p5 ∨ p1) ∨ ((p2 ∨ p1) ∧ ((p4 ∧ (False ∨ False)) → p1)))) ∨ (p4 → (False ∨ ((p5 ∧ (p5 → True)) ∨ (False → (p4 → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56186720559055199762788600181 : (((p4 ∧ ((p3 → True) ∨ False)) ∨ (((((p4 ∧ p5) ∧ (False → ((p3 → (p1 ∨ (p1 ∧ False))) ∨ (p3 → False)))) ∧ p2) ∨ p4) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56223638702149947204595022769 : (((p3 ∨ ((False ∨ p4) ∨ False)) ∨ (((p2 ∨ p3) → p2) ∨ ((False ∨ (p2 ∨ p3)) → ((True ∧ (p2 ∧ ((p4 → False) ∧ p4))) → p5)))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h15
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61500507240298307481089841324 : ((p1 ∧ ((((p2 ∨ (((p2 ∨ (p2 ∧ p1)) → p5) ∨ (p3 ∨ (p5 → (p2 ∧ p4))))) ∧ p1) ∨ p3) ∧ (((True ∨ True) → p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66639064976936518052072094022 : ((True → (((p1 → (((True ∨ p4) ∧ p4) ∨ (p5 → False))) ∧ (p1 → p2)) ∨ (((p1 ∨ p2) ∨ (False ∧ p4)) ∨ (p1 → (p5 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49638675368868093866735213956 : (((((p1 → p3) ∨ (True ∧ False)) ∧ (True → (p4 ∨ (((p4 → (p4 ∧ (p4 ∧ p1))) ∨ (p5 ∧ p4)) ∧ False)))) → (False ∧ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167060409981769147287200252326 : ((((True ∧ (((p3 ∧ ((p2 ∧ (p3 → p1)) ∨ (p5 ∨ p1))) → True) ∨ p5)) ∨ p3) ∨ True) → ((((p1 → False) ∨ (p4 → p4)) ∨ p3) ∨ p4)) := by
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
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141241217145087167136784439215 : ((((p5 → False) ∧ ((False → p1) ∨ True)) → ((((p5 → (((False → False) → p4) ∧ p4)) ∨ p4) ∧ p2) → (p2 → True))) → ((True → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299147297830649879812555738591 : (False ∨ ((((p3 ∨ False) ∨ (p1 → ((p3 → (False ∨ p5)) ∨ (((p1 ∧ (p2 ∨ p2)) → ((p4 ∨ p5) ∨ (p4 → p1))) ∨ p4)))) ∨ p2) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304778542897406571899840666025 : (p1 ∨ ((p5 ∨ ((p2 ∧ (((p2 → (p2 ∨ ((p5 → (False ∧ p2)) → p1))) ∧ (p1 ∧ False)) ∧ True)) ∧ (p5 ∨ (p3 ∨ False)))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192293098496201169474000966824 : ((((p5 ∧ p1) → (((False ∧ p4) ∨ False) → p1)) ∧ p5) → (((p2 → p4) ∧ (True ∨ p2)) ∨ (True ∨ (p4 ∧ (p4 → (False → (p4 ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249334112241727665355594207409 : ((p4 ∨ p5) ∨ (p1 ∨ ((((((True → ((True ∨ p5) ∧ p2)) → p2) → False) → (((p4 ∨ p3) ∧ p5) ∨ (False ∧ True))) ∨ True) ∨ (p1 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206968321659547806727837735325 : ((((p2 ∨ (p2 ∧ p3)) → p4) ∧ p1) → (((p1 ∧ p4) → p5) → (((False ∧ p5) ∧ p4) ∨ (((p5 ∧ p3) → (p3 ∧ (p3 → p1))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161489643331426408468089339775 : ((p4 ∧ (((((p1 → (True → False)) → p3) ∨ p3) → (((p1 → (p1 ∨ p1)) → p4) ∧ False)) ∧ p3)) → ((p2 ∧ ((p5 ∧ False) ∨ p1)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 → (True → False)) → p3) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (((p1 → (True → False)) → p3) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h20 : (((p1 → (True → False)) → p3) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h21 := h18 h20
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309635612369764915455140509170 : (p2 ∨ ((((p1 ∧ p5) ∧ (p2 ∨ p5)) ∨ ((p4 ∨ (p1 ∧ (p4 ∧ (((p1 → False) ∨ p3) ∨ p2)))) → (True → p1))) ∨ ((p3 ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57144719832155807128858904491 : ((((p4 → True) ∧ p5) ∨ (p3 ∨ ((((p3 ∧ ((p4 → (p1 ∧ p2)) → True)) ∨ (p3 ∨ True)) ∨ p4) ∧ (p1 ∨ ((True → p1) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87116103611572467792160345243 : ((((True ∨ False) ∨ ((p4 ∧ (True → True)) ∨ p1)) → ((((((p1 ∧ p3) ∧ (p2 ∨ p2)) ∧ (p5 → p2)) ∧ p2) ∧ False) ∧ (p4 ∨ p2))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ False) ∨ ((p4 ∧ (True → True)) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56917378057549885022208275361 : (((p5 ∧ (False → p4)) ∧ ((p4 ∨ (p3 ∧ p2)) → (p1 ∨ ((p2 ∨ p5) ∧ (p3 → (((True → False) ∧ ((False ∨ p5) → p5)) ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228432550795555398044205448986 : ((False ∨ (p5 ∧ p3)) ∨ ((((p5 ∨ p1) ∧ p2) → p4) ∨ ((p5 ∨ p3) ∨ ((((p1 → True) ∨ p3) ∧ p5) → (p1 → (p1 ∨ (p5 ∨ p3))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80494876239653342418386118681 : (((((p1 ∧ p3) ∨ p3) ∨ ((True ∨ ((True ∨ (p3 ∧ (((False → p1) → p4) ∧ (p3 ∧ p5)))) → (p3 ∨ p3))) ∨ p5)) → (True ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ p3) ∨ p3) ∨ ((True ∨ ((True ∨ (p3 ∧ (((False → p1) → p4) ∧ (p3 ∧ p5)))) → (p3 ∨ p3))) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_116368797760373735670246782247 : ((((p5 ∧ p4) → p2) → (((((p2 ∧ p5) → p2) ∧ p2) ∨ (((p1 → p2) → p1) ∧ (True ∨ (p4 ∨ (False ∧ p5))))) ∨ p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2341784138170194380261634043 : (((((p4 → (p5 ∨ p1)) ∨ True) ∨ p3) ∨ ((p4 → p5) → p4)) ∧ (((False ∨ p1) ∨ (False ∨ (p3 → p3))) ∨ (p5 → (p3 ∨ False)))) := by
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
theorem thm_5_vars_758290180330269824103563940866 : (((p2 ∧ (((((((True ∧ True) ∨ p4) ∨ False) ∧ p3) ∨ ((((p4 ∨ p2) ∧ p1) ∨ p2) → (p1 ∧ ((p1 ∧ p3) ∨ p2)))) ∨ True) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791936554647383024573941238992 : (((True → (((p3 ∨ (p5 ∧ True)) → ((((True → p4) ∧ (True ∨ (p5 ∧ p5))) → (p1 → False)) ∨ (False → (p4 ∨ p3)))) ∨ (True ∧ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61419728893195220704309159090 : ((p1 ∧ (((p1 → (((False ∨ (p3 → True)) → (p5 ∧ p1)) → (((p5 ∨ p1) ∧ (p2 ∧ True)) → ((p3 ∨ p2) → p2)))) → p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168633260104773301122947514890 : ((p4 ∧ ((True ∨ (True ∨ (((p4 ∨ p5) → (False → (True ∨ (p1 → p3)))) → p5))) ∧ p5)) → ((p3 → (p3 → p1)) ∨ ((p3 ∧ False) → p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h18



