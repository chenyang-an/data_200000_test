variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65048712558006979079378069333 : ((p2 ∨ (False ∧ (p4 ∨ ((p2 ∧ p2) → (((((p1 ∨ (p4 → (p1 ∨ p1))) ∧ p4) ∧ ((p2 ∨ p1) ∧ (p5 ∧ p5))) ∧ p4) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114527556926695525520640630943 : (((p1 ∨ ((p4 → (((p1 ∧ p2) ∨ (p4 → ((p3 ∨ (p3 → p3)) ∧ p3))) ∨ False)) ∨ True)) → (False ∨ (p1 ∧ (p4 ∧ False)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318602985258044269446173751702 : (p4 ∨ (((p5 → (False → ((p1 → p1) → (p3 → p2)))) ∧ (((True → p3) → (p3 ∧ (((False ∧ p1) ∨ p5) ∨ p3))) ∨ p3)) ∨ (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701320650311932672763786553859 : (((((p2 → (p3 ∨ (p3 → (p3 ∧ True)))) → (p4 ∧ p2)) ∧ (p4 ∧ ((((p1 ∨ p4) ∨ p3) ∨ True) ∧ (((p3 → p4) ∨ p5) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241440542052426418069401317627 : ((False → p1) ∧ (p2 ∨ (True → ((p3 ∨ (p5 → (p4 → True))) → ((p5 ∨ ((p4 ∧ ((p1 ∨ p5) ∧ ((p2 → False) ∨ p4))) → p1)) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678404636660790140980870733616 : (((((((p3 → True) → p5) → False) ∧ ((p1 → (True ∨ ((True ∨ (p4 ∧ (True ∨ False))) ∧ p1))) → p4)) ∨ ((p5 ∧ (True ∨ p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190607936111117855867646978316 : ((((p4 ∨ p3) → ((p4 ∨ (p5 ∧ p2)) ∧ p5)) → False) ∨ ((p4 ∧ p4) ∨ ((False → (p4 ∨ (p1 ∧ False))) ∧ (((True ∨ p1) ∧ True) → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193921862981522658709050584728 : ((p1 ∨ ((p5 ∨ p1) → (False ∧ ((False → p1) ∧ p3)))) → (p3 ∨ (False ∨ ((((p4 ∧ p4) ∨ (p4 ∨ (p1 ∨ (False → p2)))) ∨ True) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_616937923005007096949867279995 : (((((p4 ∧ (p3 → (p1 ∨ (p2 ∧ ((True → p5) ∧ p1))))) → (((p1 ∧ (p4 ∨ (p2 ∧ p1))) ∧ (p4 ∧ (p1 ∧ False))) ∨ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44507846633366471602418512859 : (((((False ∧ ((False ∨ (True ∧ p5)) ∨ (p1 → p2))) ∧ p5) ∨ ((True → p4) → (((p3 ∨ ((p3 ∧ False) ∨ True)) ∨ p1) ∧ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164728083083857547095845218677 : ((((True ∧ ((p2 ∨ (p3 ∨ (p4 ∨ p4))) → ((p1 ∨ (True → p4)) ∨ p4))) → p3) ∨ p1) ∨ ((p5 ∧ p1) → (((p4 ∧ p3) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_773445444145989458863042597042 : (((False ∨ (((((p2 → False) → (False ∧ p3)) ∨ ((p5 ∨ (((p3 ∨ p1) → (p4 ∧ p5)) ∧ p3)) → ((p4 → p5) ∨ False))) ∨ p1) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_62035986296116418741914891335 : ((p2 ∧ ((p4 ∨ p4) ∧ (((p2 → p5) → (p4 ∧ True)) ∨ (p2 ∧ (True ∨ (p4 → (p2 ∧ ((p5 ∨ (p4 → p4)) ∨ (False → p4))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590073877280562347261785493038 : (((((((((p4 ∧ (p3 ∧ False)) ∧ (p2 ∧ p4)) ∧ p3) ∨ (p1 → True)) → ((((False → False) → (p4 ∨ p5)) ∨ p2) ∧ False)) → p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232709004023128652431329438173 : ((p1 ∧ (p3 ∨ False)) → ((p3 ∧ (((p5 → (False ∨ p3)) ∧ (p4 ∧ (((p1 → p5) ∧ p4) ∨ ((p2 → (p1 → False)) ∧ p5)))) → p2)) ∨ p1)) := by
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
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733331257373053344560009542766 : ((((p3 ∧ p5) ∧ ((p1 → p2) → (((p3 ∧ p4) ∧ p4) ∧ ((((True ∨ p3) ∧ (p4 → (True ∨ (p1 ∧ p4)))) → (p1 → p2)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303833151501651562037111261530 : (p1 ∨ (((p5 → ((((p2 ∨ ((p1 ∨ (True → (p4 ∧ p1))) → (((True → p4) → True) → p5))) → p4) → False) → p2)) ∧ (p5 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326953855421837268986344082787 : (True → ((((((False ∧ (p5 ∨ p1)) ∧ (False → p5)) ∨ (p1 ∨ p2)) ∨ (p1 ∨ (False → (((p1 ∧ p5) → p2) → p2)))) ∨ (p1 ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304044125819685240015891557623 : (p1 ∨ ((p4 ∧ (p2 ∨ (((p5 → ((p2 → p1) ∨ False)) ∨ ((p1 ∨ p3) → ((p2 → (p5 → p2)) ∨ False))) ∧ ((p3 → p3) → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654498423991274972432225364700 : (((((False ∧ ((((p5 → (p3 → p4)) → (p1 ∨ (True ∨ p1))) ∨ ((((p1 ∧ p1) ∧ p1) ∨ False) → p2)) → p5)) ∨ True) ∨ (p1 ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_309967958267932422325865335414 : (p2 ∨ ((((p4 ∧ p2) → True) → (p2 ∧ (True ∨ (False ∧ (True ∧ (((p1 ∨ p4) → False) → p2)))))) → ((p2 ∨ p2) ∧ (p2 ∨ (p5 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∧ p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698330266458882166221593550195 : ((((((p3 ∨ ((False ∨ p3) ∨ (p5 ∧ True))) ∨ False) ∨ (p2 ∧ p5)) ∨ (p3 → ((((p4 ∧ (p3 ∧ p5)) ∨ p3) → False) → (p3 ∧ True)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355528566336645316591866477108 : (p5 → (((((((p4 ∧ (False → True)) ∨ p5) ∨ (True → p2)) ∧ ((((p3 ∨ p2) ∨ p5) → (p3 ∨ True)) → p2)) → p2) ∧ p1) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50030177624912210139026602843 : (((((p5 → True) ∧ (p2 → p2)) → ((p5 ∧ p4) ∨ (((p3 ∧ (p1 ∧ p2)) ∧ (p1 ∧ p5)) ∧ p5))) ∧ ((p2 ∧ p5) ∧ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810570126111639818913518290747 : (((p5 → (((False ∨ (p2 ∧ True)) ∨ False) ∨ (((p5 ∧ (p5 ∧ p4)) ∧ (p3 → ((p4 ∧ (True → (p4 ∨ p5))) ∧ (p4 → p5)))) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262475281856280361702029850073 : (True ∧ ((p4 ∨ ((p5 → p3) → ((((p3 ∨ ((p5 ∧ True) → p4)) ∧ (((((p4 → True) ∧ p2) → False) ∨ p4) → p5)) ∧ p2) ∧ True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137849263571764827804473935102 : ((p3 ∨ ((p2 → (p4 ∨ p5)) ∨ (((p4 → p3) ∧ (((False ∧ p1) → True) → p5)) ∧ (((p4 ∨ p4) ∨ p5) ∧ p2)))) ∨ ((p2 ∧ p5) → p2)) := by
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
theorem thm_5_vars_208116939641366137181199813499 : ((((p2 ∧ p2) ∨ p1) → (p4 → p1)) → (p1 → ((p5 → p4) ∨ (p1 → ((True → ((p3 → (((p2 ∨ p2) ∧ p2) ∧ p5)) → p2)) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61391871176414471371395914204 : ((p1 ∧ ((((p1 ∧ (p3 → p4)) → p1) ∧ ((((p3 → ((((p2 ∧ p1) ∨ p1) ∧ (True → p1)) ∨ True)) → p5) ∨ p5) → p4)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782968669038963586506366428760 : (((p3 ∨ (((((p4 ∨ ((True ∧ p5) ∧ ((p1 → ((p2 ∧ p1) ∧ False)) ∧ (p2 ∨ p5)))) → (p2 → p1)) ∨ p5) ∨ False) ∨ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809744602922127970302954070518 : (((p5 → (((((p2 ∧ (False ∨ (p4 ∨ (True ∧ ((p3 ∨ True) ∨ p1))))) ∨ ((False ∧ p5) ∧ True)) ∨ (p2 → p1)) ∧ p2) ∨ (False → True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_313309817197859649734269090127 : (p3 ∨ ((p1 ∨ (((((True → (p5 ∨ p5)) ∨ (p1 ∨ ((p3 ∧ (False ∨ p1)) → True))) ∧ True) → ((False ∧ p2) ∧ True)) → (p1 → False))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (p5 ∨ p5)) ∨ (p1 ∨ ((p3 ∧ (False ∨ p1)) → True))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199249564572471516577875208498 : (((p3 → ((p2 ∨ (p2 ∧ True)) → p5)) ∧ p4) → (((False ∨ p5) → ((((True → True) ∧ p1) ∧ ((True ∧ (p5 ∧ p5)) ∧ p2)) → p3)) ∨ p4)) := by
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
theorem thm_5_vars_305805421786517196566195742119 : (p1 ∨ ((((p3 → False) ∨ p4) ∨ ((p1 → p3) ∧ p1)) → ((((p3 → p3) → False) ∧ p3) → (p5 ∧ (((True ∧ False) ∨ (p4 ∨ p1)) ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h16
    -- False on the left can always be used.
    apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668945601394509522680831149188 : (((((p3 ∨ ((((p5 ∧ p1) ∨ ((True ∧ p4) ∨ p4)) ∧ p3) → (p5 ∨ (p2 ∨ (p2 ∨ (False → True)))))) ∨ p3) ∨ (False ∧ (p2 → p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130948655197120458324239657587 : (((((False ∧ False) ∨ (p5 → (True → p1))) ∧ (p3 → (p3 ∧ p1))) → ((p3 → (p5 ∧ p3)) ∨ (p1 → (False → True)))) ∧ (False → (p4 ∧ p3))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113931334669758026254286739653 : (((((p4 ∨ ((p4 ∨ p4) ∨ p1)) ∨ (p5 ∨ (False ∨ p1))) ∨ (((p3 ∧ (p3 ∧ p3)) → p2) → True)) ∧ ((True ∧ p2) → True)) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300332446071986770757140562751 : (False ∨ (((True → False) → (((((True ∨ p3) ∨ (False → (((True → (True → p5)) ∧ True) → False))) ∨ p3) ∧ p3) ∨ p3)) ∧ (p1 → (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351260900748049490869544224034 : (p4 → ((p1 ∨ (((False ∨ ((False → p5) → p4)) → ((p5 ∧ p2) → (((p2 ∨ p4) → (p2 → False)) ∧ p1))) → p3)) ∨ ((p1 ∨ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632355752100087179115697624158 : (((((p5 ∧ ((((True ∨ p2) ∨ (((((p4 ∧ p5) ∨ p2) ∨ (p3 ∧ p4)) ∧ p5) → p1)) ∨ p2) ∨ (p4 ∨ (True ∧ p5)))) → True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642963946695434870426165456820 : ((((p2 ∧ ((((p3 → (p2 → p3)) ∨ False) ∧ True) ∧ (((p3 → (p1 → (p5 → p2))) ∧ (p4 → ((p2 ∨ p1) ∨ p5))) ∨ True))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232822896049883634835039976850 : ((p2 ∧ (p2 ∨ p1)) → (p1 → (p5 ∨ (((p3 ∨ True) ∨ True) ∧ (p5 ∨ ((p4 → p3) ∨ ((((p5 → p3) → False) ∨ (p4 ∧ True)) ∨ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766810231116911212276777498914 : (((p4 ∧ (p3 ∨ ((p5 ∨ p5) ∧ (p1 → (p2 → (((p3 ∨ (p1 ∨ False)) → (((p4 ∨ True) → p3) ∧ ((True ∧ p4) ∧ p3))) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185227914568685298490492397684 : ((False ∧ ((True ∧ (p1 → (False → (p1 → p5)))) → (p4 ∨ p2))) ∨ ((p4 → (p4 ∨ (p2 ∨ (p3 ∧ p3)))) ∨ (p5 → ((p5 ∨ p4) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52611650535509400803040688745 : (((((p1 → (p5 → p1)) ∧ p5) → (p1 → ((p1 → (p3 → p2)) → p2))) ∨ (p3 → (p2 ∨ ((p5 ∨ p4) ∧ ((p3 ∨ True) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171831107996684058507654580623 : ((((True → (p1 ∨ p5)) ∧ ((False → (True ∨ p3)) ∧ ((p5 → p3) → p4))) → p2) ∨ ((False ∧ ((((False ∨ False) → p5) → p4) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629168579573115944082666964144 : (((((((p1 → (p5 → False)) → ((p5 → ((p4 ∧ p4) ∨ (False ∨ ((p1 ∧ p2) → p5)))) → ((p2 ∨ p4) → p2))) ∨ True) ∨ False) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718766897246983878886779016838 : (((((p3 ∧ p2) ∨ (p4 → p2)) ∨ ((p1 ∨ (p2 ∨ ((p3 ∧ p3) → (p5 → (((p1 → (False → p2)) ∨ (p2 → False)) → True))))) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_559437197981351019310081103884 : (((p4 ∨ (((p5 ∨ (((p4 → (False ∨ ((True → (p1 ∧ (p5 ∨ p3))) → p1))) ∨ p2) → p2)) ∨ (p3 ∧ (True ∧ True))) ∨ (True ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310548140513740969070530230228 : (p2 ∨ ((True ∨ (((p3 ∧ p3) ∨ p1) ∧ False)) → (False ∨ ((((p3 ∨ True) ∨ ((True → p1) ∨ (p5 ∧ p5))) → p2) ∨ ((p5 → p5) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606626142307417108854577928930 : ((((((False ∨ (p4 → ((((False → p3) → p4) ∨ (False → p4)) → ((False → ((p3 ∧ False) → p4)) ∧ (True ∨ True))))) → p4) ∧ p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711450910590464021574770850313 : ((((p4 ∨ ((True → p3) → (p5 ∨ p2))) ∧ ((((((True ∨ p4) ∨ p4) ∨ (p2 ∨ p1)) → (True ∨ False)) ∧ p5) ∨ ((p2 ∨ p1) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52354036969833655053553940692 : (((((((p4 ∧ p2) ∨ p1) ∧ ((p2 → p2) ∨ False)) → p2) ∧ (p5 → p4)) ∧ (((p4 ∧ (p3 ∧ True)) ∧ (p5 → (p2 → False))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227126698181762074557018686522 : (((p4 ∨ p4) → p1) ∨ (p3 → (True → (p3 → (((False ∧ (((True ∧ (p3 → ((p2 → p2) → False))) ∨ p1) ∨ p3)) ∨ p5) ∨ (p4 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133528019036142871976459001434 : (((((True ∨ (p3 ∨ ((p2 ∨ True) ∨ ((False → p2) ∧ ((p5 ∧ p5) → p5))))) → (p3 ∨ (p4 ∨ p3))) ∧ False) ∧ p1) ∨ ((True ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351930049043540438283466242054 : (p4 → ((((p1 ∨ p5) ∨ (True ∨ ((True ∨ p1) ∧ p4))) ∨ p5) → ((True → (p1 → (((False ∨ False) ∨ (False → p4)) ∨ (p3 ∧ p2)))) ∨ p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h22
          -- Implications on the right can always be decomposed.
          intro h23
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h26
          -- Implications on the right can always be decomposed.
          intro h27
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- False on the left can always be used.
          apply False.elim h28
  case inr h29 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h32
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263136180716706217522875564032 : (True ∧ ((((False → True) → True) ∧ (((p4 ∨ True) → ((p4 ∨ (True ∧ (p5 ∧ True))) → (True → (p5 → (False ∧ p4))))) → False)) ∨ (p1 → True))) := by
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
theorem thm_5_vars_56469993139644642469899508717 : ((((p2 ∨ p3) → (p3 → p2)) → ((p1 → False) ∧ (((False → (((True ∧ p1) ∧ ((p2 → (p3 → True)) ∧ True)) ∧ p3)) ∧ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597400711506354228264577163945 : (((((((p5 → p5) → p5) ∨ p4) ∨ (((p3 ∧ p3) ∧ ((p5 → True) ∨ (p4 ∧ ((((True → True) ∧ p2) → p2) → False)))) ∧ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148679352851496515310143094914 : (((((p3 ∨ (True ∧ p5)) ∨ p1) ∨ (p4 ∧ p3)) ∨ (((p3 → p3) → True) ∨ (p4 ∨ (False ∧ (False → p4))))) ∨ ((True → (True ∧ p2)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14859322236956392028166811233 : (((((True → p4) → ((True ∧ False) ∨ ((False ∧ False) → p2))) → ((((False → (p4 ∨ (p1 → p1))) ∨ p5) → False) → p5)) ∨ (p1 ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False → (p4 ∨ (p1 → p1))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122826148985556570574159177588 : (((((((False ∨ True) ∨ ((True → p4) ∨ (True → ((p5 → False) ∨ p3)))) ∧ p3) ∨ (True ∧ p4)) → p3) ∧ ((p4 ∨ p4) ∧ p4)) → (True → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((((False ∨ True) ∨ ((True → p4) ∨ (True → ((p5 → False) ∨ p3)))) ∧ p3) ∨ (True ∧ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((((False ∨ True) ∨ ((True → p4) ∨ (True → ((p5 → False) ∨ p3)))) ∧ p3) ∨ (True ∧ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180331679916692121538106341577 : (((p1 ∧ ((((p2 ∨ (p5 ∨ p3)) → p5) → p2) ∨ True)) ∧ (p5 ∧ True)) → ((((p2 → False) ∨ (True ∨ False)) ∨ (p1 → p2)) → (p2 ∨ p5))) := by
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
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h6.left
        let h11 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h6.left
        let h14 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h18.left
          let h23 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h18.left
          let h26 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h29.left
    let h32 := h29.right
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h30.left
      let h35 := h30.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h30.left
      let h38 := h30.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42725479534926588628895476668 : (((True → ((p4 → (((((p5 ∧ (p1 → (p3 ∧ False))) ∨ ((p1 ∧ p2) → p2)) ∧ p3) → ((True → p3) → False)) ∨ True)) ∧ p1)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246132151127574716382270634670 : ((p4 ∧ p2) ∨ (((False ∨ (p4 → ((p4 ∧ True) ∧ (p3 → (p5 ∨ ((p4 ∨ (p4 ∧ ((False → False) → p5))) ∧ True)))))) ∧ (False ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61714204272091101091799389385 : ((p1 ∧ (p5 ∨ ((p2 → p3) ∨ (p2 → ((p5 ∧ (((p1 ∨ p3) → ((p5 ∨ (p2 ∨ True)) ∧ (p2 ∨ p1))) ∨ (True ∧ p4))) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149467420381861438220548194877 : ((False ∧ ((True ∨ (True ∨ p5)) → (((p1 ∧ (p3 ∨ (p2 ∧ (p4 → (False ∧ p4))))) ∨ p1) ∨ (p3 → p1)))) ∨ (True ∧ (False → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624836077622366148914355002547 : ((((p5 ∨ ((((p1 ∧ ((p5 → p3) ∨ (p2 ∨ p3))) ∧ (p5 ∨ (p1 ∧ p3))) ∨ ((p1 ∧ (p2 ∨ p5)) ∨ p2)) → (p2 ∨ True))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39017363187940356495122459956 : ((((True → p3) ∧ ((((p3 ∨ (((p1 ∨ p3) ∨ False) → p4)) ∨ (((False ∨ True) ∨ p2) → False)) → p4) ∨ ((p5 → p4) ∧ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148703119180989177901002652384 : ((((((False ∨ False) → False) ∧ (p3 ∧ p5)) ∨ p1) → ((p2 ∧ (True → ((p3 ∨ p2) ∨ True))) ∧ (True ∧ p1))) ∨ (True ∨ ((p4 ∧ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48349895163264099662640965911 : (((p3 ∨ ((True ∨ p4) ∧ (p5 ∨ (p5 ∧ (p2 ∧ ((p4 → p4) ∧ ((True ∧ p5) → (p3 ∨ ((p4 → p1) ∧ p1))))))))) → (p2 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208359048138277313737894144062 : (((True ∧ p5) ∨ (p4 ∧ (p5 ∧ p1))) → ((p3 → ((p5 → p2) → (((p2 → (p2 ∧ False)) ∧ (p5 ∧ (p4 ∨ (False ∨ True)))) ∨ p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41143619572212772958226549458 : ((((((((p5 ∨ (p5 ∨ p2)) ∨ (p5 ∨ p3)) ∨ p4) ∨ p2) ∨ ((True → p1) ∨ (p2 ∧ (p1 → p3)))) ∨ (p2 → (p4 ∨ p2))) ∨ p4) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339605709516689209971481942900 : (p1 → (p2 ∨ ((False ∨ (((p2 → (p5 → (((p4 ∨ (p2 → True)) → (False → p3)) → False))) → p3) → (p3 ∨ ((p3 ∧ p4) ∨ True)))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677625585808436380483947508573 : ((((((((p5 ∧ ((p4 ∧ True) ∧ ((False → False) ∨ p4))) → ((False → p1) ∨ p1)) ∨ p2) → p1) → p4) ∨ (True ∨ (p1 ∧ (p4 ∨ p1)))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_228078714682821821564769425850 : ((p4 ∧ (p5 ∧ p4)) ∨ (((p4 ∧ (((p5 → (p3 ∧ ((p4 → p4) → (p4 → (p4 ∨ (p3 ∨ (False → True))))))) → False) ∧ p4)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160536162170740136123533457502 : ((((p1 → (p3 ∧ False)) ∧ (((True → (p1 ∨ p2)) → p1) → True)) ∨ (True ∨ (p3 ∧ (p5 ∧ True)))) → (p1 → (((False → p5) ∧ p3) → p3))) := by
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
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69380954523692619607582705857 : ((p5 → (p1 → (((p5 ∧ p1) ∧ ((((p4 ∧ p3) ∧ (p5 ∧ (False ∨ p3))) ∨ False) ∨ (((True ∨ p4) ∨ False) → p1))) ∨ (True → p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199067314649927585306286731542 : ((((((False → p5) ∨ p2) ∨ True) → p4) ∧ p1) → (((p3 ∧ p3) ∧ (((False → ((p2 ∧ p1) ∧ (p2 ∨ (False ∧ p2)))) ∧ p2) → p5)) ∨ p1)) := by
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
theorem thm_5_vars_51270856236510236744314952867 : (((True ∧ (((False ∨ (((False ∧ p1) ∨ p4) ∧ p1)) ∧ ((p5 → p5) ∨ (p4 ∨ p2))) ∨ p3)) ∨ ((((False ∨ p1) → p5) → p5) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207100026488751312427972798962 : (((False ∨ (True → (p3 ∧ p1))) ∧ True) → (False ∨ ((((p4 ∧ ((p3 ∧ ((True ∨ p2) → True)) ∨ (p2 ∧ p3))) ∧ True) ∨ p1) → (p3 → p1)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303076969185408310651807697071 : (False ∨ (p2 → ((False ∧ p3) ∨ (((((True ∨ False) → ((p4 → p3) ∧ (p4 ∧ False))) ∧ p5) ∧ p3) ∨ (((p1 ∨ True) ∨ (p2 ∧ p5)) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163478963418286007348117611826 : ((((p1 ∧ False) ∧ p2) ∨ ((True ∨ p1) ∨ (((True ∨ p1) ∧ p5) → ((p1 ∨ p4) ∨ p3)))) ∧ ((p2 ∨ (p1 → p2)) ∨ ((p1 → True) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234096438387473747360883959119 : ((True → (p4 ∧ p5)) → ((False ∨ ((p5 → ((True ∧ ((((p4 ∧ (p4 → p3)) ∨ p4) → p1) ∧ (True ∨ p4))) ∧ False)) → p1)) ∨ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39748956116179798391343294134 : (((True → ((p2 ∧ ((p4 → ((False ∨ True) → p2)) → ((p4 ∧ p3) ∧ ((p1 ∧ True) → (True → ((p5 ∧ p2) → p3)))))) ∧ p5)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153078243952568176062557967709 : ((p3 ∧ (((False → True) ∨ p4) ∨ (((p4 ∨ p3) ∧ p2) ∨ (False → (p4 ∨ ((p5 ∧ False) ∧ (p4 ∧ p5))))))) → ((p3 → False) → (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h22
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h28 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h29 := h2 h28
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h36 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h37 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h38 := h2 h37
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48849735705966770362045972077 : (((p2 ∨ ((p4 ∨ (((p1 ∨ ((p1 ∧ (True ∨ p2)) ∨ p5)) ∧ p3) ∧ (p5 ∨ p2))) ∧ (p5 → (p5 → p1)))) ∧ ((True ∧ p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309368791698900316319114182354 : (p2 ∨ (((p5 ∧ (p1 ∨ p4)) ∨ (p2 ∧ ((((p4 ∧ False) ∧ False) ∧ ((False ∨ p5) ∧ True)) ∧ ((p3 ∧ p4) ∨ (p3 ∨ p5))))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187258125447359015360061659620 : ((True ∧ (p1 ∨ ((True ∨ p5) ∨ (p5 ∨ ((False ∧ True) ∨ p4))))) → (((p3 ∧ p1) ∨ True) → (p3 ∨ (p5 ∨ (True ∧ (False → (p4 → p4))))))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- False on the left can always be used.
            apply False.elim h17
          case inr h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h4
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h24
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h29
          -- Implications on the right can always be decomposed.
          intro h30
          -- False on the left can always be used.
          apply False.elim h29
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- False on the left can always be used.
            apply False.elim h36
          case inr h38 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h39
            -- Implications on the right can always be decomposed.
            intro h40
            -- False on the left can always be used.
            apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114672363778833170436753891625 : (((True ∧ (((p4 → (p4 → p3)) ∨ ((p3 → p2) ∨ (p1 ∨ p3))) → (p2 → False))) ∨ ((False ∧ p4) → (p1 → (p1 ∧ False)))) ∨ (p5 → p3)) := by
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
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215705757695950866622906087011 : ((False ∨ ((True ∨ p3) → p3)) ∨ (p4 ∨ ((p3 ∨ p4) ∨ ((True ∨ True) ∨ ((p3 → (p5 → (p1 → p5))) ∨ (p5 ∨ (p1 ∧ (p3 ∨ p5)))))))) := by
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
theorem thm_5_vars_317625061462897858171447432675 : (p4 ∨ ((((((p4 → (((((False ∧ p5) → False) ∧ p4) ∨ p1) → p2)) ∧ ((p3 ∧ True) → p2)) ∨ (p1 → False)) ∨ (p4 ∧ False)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305625206387316573024937228062 : (p1 ∨ (((False → p2) → (((p4 ∨ (False ∨ True)) → True) → (False ∧ p3))) → ((p4 ∧ (p1 ∧ p4)) ∨ (p3 → (((p1 ∨ p2) ∧ p1) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ (False ∨ True)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207870191093354620836117423245 : ((((p2 → p4) ∨ p4) ∧ (p3 ∨ p4)) → (((p1 ∨ (p3 → (True ∧ ((False ∧ p1) ∧ (p4 ∨ p5))))) → (p3 → p4)) ∨ (p2 → (p2 ∧ p3)))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215337743300934516681046689548 : ((p1 ∧ (p5 ∨ (p2 → False))) ∨ ((((False ∨ p5) ∧ (p4 ∧ p2)) → (((((False ∨ p4) ∨ p3) ∨ p3) → p2) → p1)) ∨ ((True → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61425995077909461811299453567 : ((p1 ∧ ((((p2 ∧ p1) → (p3 ∧ ((True ∨ p4) ∨ (((p4 ∧ p4) ∨ p1) → (False ∧ p4))))) → (False → (p3 ∨ (p2 ∨ True)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117892481526293337972406070698 : ((p5 ∧ ((((p5 ∨ p4) ∧ ((((p5 ∧ p1) ∧ False) ∨ (p3 ∧ p2)) → p4)) ∨ ((p1 → (p4 → p1)) → p5)) → (p5 ∨ p3))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234754500386462192511937787178 : ((p4 → (p2 → p5)) → ((((p5 ∧ True) ∧ p5) ∨ (p1 ∨ (p1 ∨ True))) ∨ (p3 ∨ ((p5 ∨ p3) → (p4 → ((p5 ∨ True) ∧ (p4 ∨ p1))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582349209084089978168831696909 : (((p5 → (((((p5 ∧ (p2 ∨ p4)) ∧ p5) ∧ (p5 → (p3 ∨ ((p1 ∧ p1) ∧ (((p2 ∧ p1) ∧ (False ∨ p4)) → p2))))) ∨ True) ∧ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671557492722344474218412243265 : ((((p4 → ((p3 → p5) ∨ ((p3 ∧ (p4 ∨ ((False ∨ ((p2 → (True → (False ∧ p4))) → p1)) ∧ p5))) ∨ p1))) ∨ ((False ∧ p1) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



