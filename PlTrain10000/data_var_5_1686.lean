variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165634090171638713390067331770 : ((((p2 → p5) ∨ (False ∧ (p1 ∧ p4))) ∧ (False ∨ (((p2 ∨ p1) → p1) ∨ (p2 ∨ p4)))) ∨ (((p3 ∧ (p5 ∨ p5)) ∨ False) → (p3 ∨ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112555261073160238436764478676 : (((((True ∨ p1) ∨ (((p5 ∧ (False ∨ (p4 → (p5 ∧ True)))) ∨ (p2 ∧ (True ∧ p2))) ∧ (False → (p1 ∧ p3)))) → p2) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252277992923880210195066548765 : ((p4 → p5) ∨ (((p1 ∨ p2) ∧ (((True ∧ p3) → ((p2 → p5) ∨ (p1 ∨ (((p5 ∨ (p5 ∨ False)) ∨ p4) ∨ p5)))) → p4)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40432034194968031418079340469 : (((((((((p5 ∨ True) ∨ p1) ∨ (p3 ∧ True)) → True) ∨ p3) ∧ (False ∨ (((p5 → ((True → True) ∨ p2)) → p3) → p1))) ∨ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178259333061672617756512541023 : ((((((p3 → (False → p5)) → p2) ∨ False) ∧ (p1 ∨ p4)) ∧ (p1 ∧ p4)) ∨ ((False ∧ p1) → (True → ((p3 ∨ p3) ∧ ((p3 ∧ p1) → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248413265880091540047758692460 : ((p2 ∨ p4) ∨ ((p1 ∨ p3) ∨ (p1 ∨ ((p4 → False) → ((((False → (p5 → ((p5 ∧ True) ∨ p3))) ∨ (True ∧ p1)) ∧ (False ∧ True)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55454231430330278650411276220 : ((((True ∨ (p3 ∧ (p3 ∨ p1))) → False) → (True ∧ (((((p3 ∧ (p2 → ((p1 ∨ (p5 ∧ True)) → p2))) → p2) ∨ p5) ∨ p3) ∧ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p3 ∧ (p3 ∨ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117360219307949997423753257220 : ((False ∧ (False ∨ (p2 ∧ (((((((p5 → (False ∨ p4)) ∧ (p5 ∨ p1)) → False) ∨ p5) ∨ False) ∧ p3) → ((p5 ∧ p3) ∧ p1))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38894846268809483315557804386 : (((((p3 ∨ False) → p4) ∨ ((p2 ∧ ((((((True ∨ (p2 ∧ False)) ∧ ((p3 ∧ False) ∧ p4)) → True) ∨ p1) → p4) ∨ p4)) ∨ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33689306503412461011677808836 : ((p5 ∨ ((((p2 ∧ (((False ∧ (((((False → p4) ∨ p3) → (p1 ∨ p1)) ∧ True) ∨ p3)) ∨ p5) ∧ p3)) ∨ (p5 ∧ p1)) ∨ True) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713411037204447886110286671625 : ((((p1 → (p4 ∧ (p5 ∨ (True → p3)))) ∨ ((p2 ∨ True) → (p4 ∨ (p4 ∧ (((((p3 ∨ False) ∨ False) ∨ p4) ∧ p1) ∨ (p1 → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1499581308679067709914399840 : ((((((p2 → p1) ∧ p3) ∧ (((p5 ∨ (p1 → p1)) → p3) ∧ ((p2 → False) → False))) → p5) ∨ ((p3 ∧ p3) → p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1965332780081002654833618612 : ((((p1 → p5) → p3) → ((p2 ∨ ((p2 ∧ False) ∧ ((False ∨ (True ∧ p2)) ∧ p5))) ∧ (p1 ∨ False))) ∨ (True ∨ ((p4 → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133843731981460008646844785765 : (((True ∧ ((p2 ∨ (((p2 → ((True → (False ∨ (False ∨ (p3 → p3)))) → p2)) ∧ (True → p2)) ∧ True)) → p3)) ∧ p3) ∨ (p2 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192281410412471860032019531369 : ((((True ∧ True) ∨ (p5 ∧ (True → (True ∨ False)))) ∧ p3) → ((((p4 → ((((p3 ∧ p4) → p2) ∨ p1) → p1)) ∨ p4) → p4) ∨ (False ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607020241388629415019696302517 : (((((((p3 ∨ p2) ∨ ((p1 ∧ p2) ∧ (False → ((p2 ∨ False) → p5)))) ∧ (((True → p1) ∧ p5) ∧ (True → (p2 ∨ p2)))) ∧ False) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_159565045485310091764735755378 : (((p3 ∨ (((p3 ∨ ((p1 ∧ ((False ∨ p5) → (p4 ∨ p3))) ∧ p5)) ∧ (p2 → p5)) → True)) ∧ p4) → (p3 → ((p5 ∧ (False ∧ p2)) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457516784725714728811252026571 : (((((p4 ∧ (((True ∧ (p5 ∨ ((True → p5) ∧ p4))) → True) ∧ ((p5 ∧ p4) → p2))) → False) ∨ ((((False ∨ p2) → False) → p5) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_40339178923055950030148460226 : ((((((False ∨ (p3 ∨ p2)) → (((p1 → ((False → (((p5 ∨ p2) ∨ (p5 ∨ p5)) ∧ True)) → p5)) ∧ p1) ∨ True)) ∨ p3) ∨ p2) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_257999334171906207669782169897 : ((p4 ∨ p1) → ((((p1 ∧ ((p2 → p5) ∧ False)) ∨ p5) → p3) ∨ (p4 ∨ (((((p4 → False) ∨ False) → False) ∨ True) ∨ ((p3 ∨ p5) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
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
theorem thm_5_vars_133907551991162310605277778214 : (((p2 ∨ (((p4 → (p4 ∨ (p3 ∨ p1))) ∧ p4) ∧ ((p4 → ((p2 ∨ (p3 ∧ p5)) ∨ (p2 ∧ p2))) ∧ p4))) ∧ False) ∨ ((True ∧ True) ∨ False)) := by
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
theorem thm_5_vars_962601449869473069073601141700 : ((((True → p5) ∧ ((((p5 ∨ (p5 ∧ p2)) ∨ True) ∧ (False ∨ ((True ∧ (p5 ∨ ((p1 ∧ (p2 ∨ p5)) → p4))) → p3))) → (p4 ∧ True))) → p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_581366510623491339991038906405 : (((p4 → ((p2 ∨ p1) ∨ (False ∨ (p5 ∨ (((p5 ∧ (((p3 ∨ (((p5 → (True → p4)) ∨ p5) ∨ p5)) ∨ p1) ∧ True)) ∨ p4) ∧ True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43617974642058812324725563076 : ((((((False ∨ p4) → ((((True ∧ p5) ∨ True) ∨ ((p1 ∨ True) ∧ ((p4 → p2) → (p3 ∧ True)))) ∨ (False → False))) → False) → p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708362519001788702627651402145 : ((((((p4 → (False → False)) ∧ (False → p2)) ∧ p2) → (((True ∨ (p5 → p1)) ∧ (p4 ∨ (True → p5))) ∨ (True ∨ ((True → p3) ∨ p1)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185253745404358665407386859034 : ((p1 ∧ (((True → p1) ∧ (p4 ∨ (p2 ∧ (p4 → p3)))) → p3)) ∨ (((False → (((p3 ∨ p5) ∧ (p1 → p4)) → p4)) → (True ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65746167147029008149272495762 : ((p4 ∨ ((((((p3 → True) → p1) ∧ ((p5 → (((True ∧ (p3 ∧ p4)) → p2) ∨ p4)) ∧ p5)) ∨ p2) → False) → (p2 → (True ∧ p5)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p3 → True) → p1) ∧ ((p5 → (((True ∧ (p3 ∧ p4)) → p2) ∨ p4)) ∧ p5)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204821968475143591864753459915 : ((((True ∧ (p3 → p1)) ∨ p3) → p1) ∨ ((((p5 ∧ (p3 ∧ (False → (False ∧ p5)))) ∨ p2) ∨ ((True ∧ (p4 → (True → True))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155837688227973375007722494294 : ((True ∧ (False ∨ (p3 ∨ (True ∨ ((False ∨ p4) ∨ (p3 → (((p3 ∧ p2) → (False → p1)) ∧ p5))))))) ∧ (((p1 → p3) ∨ (p3 ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89360829883890030620721138644 : (((True → (p3 ∧ False)) ∧ (p2 → ((p5 ∧ (False → ((((False → (p1 ∨ (p2 ∧ p1))) ∨ ((p2 → True) ∨ p1)) ∨ p2) ∧ p1))) ∨ p4))) → p1) := by
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171242421064541210253073768668 : ((p4 → ((((p2 → (p3 → (p4 → (p2 → p4)))) ∨ p2) → p2) ∨ (False → p5))) ∧ ((True ∧ p3) → ((p3 ∨ ((True ∧ p4) ∨ p5)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134718950408616048709596016345 : (((((p1 ∨ True) → False) ∨ ((((True → ((p4 ∨ ((p1 → p1) ∧ p5)) ∧ p5)) → (False ∨ p1)) ∧ p5) → p1)) → p2) ∨ ((p4 ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779514343742672273365266133525 : (((p2 ∨ (((p1 → (p4 ∧ (p4 ∨ False))) ∧ ((p4 ∨ ((p2 → p5) → False)) ∧ ((((p4 ∨ False) ∧ (False → p2)) ∨ p1) → p5))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_198651467092071939744172410575 : ((p3 ∨ (p1 ∧ ((True → p3) ∧ (p2 ∨ False)))) ∨ ((((p2 → ((((p4 → False) → p1) ∨ (p2 ∨ p1)) ∧ (p5 → p5))) ∨ True) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179035740074422043280600401139 : (((p5 ∨ p3) → (((p4 ∨ (((p2 → p3) ∧ p2) ∧ p3)) ∨ p2) ∧ True)) ∨ (((p2 → (False ∨ p5)) → ((p4 → True) ∨ p5)) ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119216580799826518438523241092 : ((p2 → ((((p1 ∨ p1) → p3) ∧ (p5 ∧ p2)) → (p1 ∨ (p4 ∨ ((False ∧ p5) ∧ ((True ∧ (p3 ∨ True)) → (False ∨ p2))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299273312458906729893742871134 : (False ∨ (((((p2 → (p1 → True)) ∧ (p5 ∧ p3)) ∨ (p1 ∨ (((p1 → False) ∧ False) → p5))) → ((p2 ∨ ((p5 → False) ∨ False)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117432044005900170166123763063 : ((p1 ∧ ((p5 ∨ (((False ∧ (p4 ∨ (p2 → p3))) ∨ p1) → ((p1 ∨ p4) → p2))) ∧ ((((p4 ∧ p2) → p5) ∨ p5) ∨ False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609854878823406272498552347475 : (((((p1 → ((True ∨ ((((p2 ∧ p1) → p3) ∧ p4) ∧ ((True ∨ (p5 → True)) ∨ p4))) ∧ (p4 ∧ ((p2 → p5) ∨ p4)))) ∨ p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41157790580643208883473400024 : ((((p4 ∧ ((p3 ∨ (p5 ∨ p3)) ∧ ((p2 → (p2 ∨ True)) ∨ (p1 → (p5 ∧ ((False ∧ p3) ∧ False)))))) ∨ ((True → p4) ∧ p1)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47170087325859574727277065726 : ((((((((p5 ∧ (False → False)) → p5) ∨ (p5 ∧ (p1 → False))) ∨ p5) → False) ∨ (p4 ∧ ((p1 ∧ p4) ∨ (p3 ∧ True)))) ∨ (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34460740233539095069124730227 : ((True → (True → (p2 ∨ (((((p4 ∧ ((p3 ∧ p1) → p5)) ∨ (p3 → (p1 → p1))) ∧ (True ∧ p4)) → p2) ∨ ((p3 ∧ False) → p1))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173977757600343939076679659681 : ((((p2 → (p3 ∧ True)) ∨ (((True ∨ p4) ∨ ((False ∨ False) ∧ p3)) → True)) → p4) → (p1 ∨ ((p4 ∨ p4) ∨ ((False ∧ (p5 ∧ True)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → (p3 ∧ True)) ∨ (((True ∨ p4) ∨ ((False ∨ False) ∧ p3)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50216146695557029780389336246 : (((((p3 → (p2 → ((p4 ∨ False) ∨ False))) ∨ (p1 → (p2 → (p1 ∧ (p1 → (p5 → p3)))))) ∨ p3) ∨ (False ∨ ((False ∧ p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136601380632132447266924793374 : (((True → (p1 ∧ True)) ∨ ((True ∨ (False ∨ p1)) → ((True → ((p1 → (p2 ∧ (False → p3))) ∨ p3)) → (False ∧ True)))) ∨ ((False → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178082959137290846745805192891 : (((((((p5 ∧ True) ∨ (p5 ∨ p5)) ∨ p1) ∧ (p2 ∧ p3)) → p5) → p2) ∨ (p5 ∨ (False → ((p3 ∧ (((p5 → p1) ∧ False) ∧ p1)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139379215599343332226584011433 : (((p3 → (((p5 ∧ (p1 → p3)) → ((p2 → ((p2 → p5) → (p3 ∧ p4))) ∨ True)) → (False ∨ (p1 ∨ False)))) ∨ p4) → ((p4 ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_68478294080439791142169924531 : ((p3 → (p5 ∧ (p5 → (p1 ∧ ((True → (((((p2 → (p4 ∧ False)) ∧ True) → p4) → (False ∧ p3)) ∨ (p3 ∧ (p1 ∨ p3)))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174303441094756226624735330141 : ((((True ∧ ((p5 → p2) ∨ ((p1 → p2) ∨ p4))) → p3) ∨ ((p5 ∨ False) ∧ p2)) → ((p5 → ((p1 → False) ∨ (p1 ∨ (p1 → p5)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45019769434096286215844811325 : ((((True ∨ p2) ∨ ((p2 → ((p1 ∨ True) → (((p4 ∧ p5) → p4) → (p5 ∧ ((p1 → False) ∧ (True ∨ p3)))))) → (p3 ∧ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178721233420220695033258459166 : (((((p5 → p5) ∨ p4) ∨ p4) → (p1 ∨ (((False ∨ p5) ∧ True) → p4))) ∨ (p4 → (p5 ∨ ((p3 ∨ p1) → (True ∧ ((p3 → p3) ∨ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520059258405178074444642299267 : ((((p3 ∨ True) → ((((((p3 → p1) ∧ p2) ∨ p2) ∧ p2) ∨ True) ∨ ((((p5 ∧ (False → False)) → True) → ((p4 ∨ p3) → False)) ∧ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_65122218706706064693852076190 : ((p2 ∨ (True → (p3 → ((((p5 ∧ (((True ∧ p2) ∨ p5) ∧ (((p4 → False) → ((p5 ∧ True) ∨ p1)) ∨ p1))) ∨ p3) ∨ False) ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340103265612444770128510290799 : (p1 → (p3 → (((p2 ∨ ((p4 ∨ (p5 → True)) ∨ ((p5 → p5) ∧ p4))) → (p2 ∨ ((p5 ∨ p1) ∧ (p4 ∨ p3)))) ∧ ((p4 → p3) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148369429557089789814378832878 : ((((((p4 ∨ False) ∧ (p1 → (p5 → (True ∧ (p3 ∧ p2))))) → p2) ∨ p5) ∨ ((p3 → (p3 ∨ p2)) → True)) ∨ (False ∧ (False ∧ (True ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216084450587804205512330786883 : ((True → ((False → False) ∧ p3)) ∨ ((((p1 ∧ p3) ∨ (((False ∧ ((p2 ∨ (False → False)) ∨ p3)) ∧ False) ∨ p4)) ∨ False) ∨ (p5 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_114283514256447082857160855177 : ((((((((p4 ∨ p2) → False) ∧ p3) ∧ ((True → p1) → (p4 ∧ p4))) ∨ (p4 ∧ True)) → p5) ∧ ((True → (False ∨ p5)) → p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169505058042104871750593136786 : ((((True → p2) → ((((p5 → False) → p3) ∧ p1) ∧ ((p3 ∨ p4) ∨ p3))) ∨ True) ∧ ((False ∧ (True ∧ (((p3 → p5) ∧ p2) ∧ p2))) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656352710545195537504003179688 : ((((((((False ∧ p5) → False) → ((p4 ∧ p2) → (p3 ∧ p5))) → p3) → ((p3 → p1) → ((p4 → p4) → (p5 ∨ p5)))) ∨ (p4 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_341980313506885595194977831080 : (p2 → (((((p1 ∨ (((True ∧ True) ∧ p2) → (p5 → (p1 → True)))) → p1) ∨ (False ∨ (False ∧ False))) ∨ (p2 ∧ p1)) ∨ (True ∧ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46292093153410153399831677482 : ((((p3 ∧ ((((p3 ∧ (True ∧ p5)) ∨ True) ∧ ((p1 ∨ False) ∨ (False → p2))) ∧ (p1 ∨ p2))) ∨ ((False ∧ p4) → False)) ∧ (False → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113214704253312770904515549486 : ((((p4 ∧ ((p5 → p4) ∨ ((((False ∧ (p5 ∨ p3)) ∨ False) ∨ False) ∧ (((True → p2) ∨ True) ∨ False)))) ∨ True) ∧ (p5 ∨ p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201353280243260253166720642460 : ((p5 → (p4 → (((p5 ∧ True) ∧ p5) → p4))) → ((p2 → (True → (((p3 ∨ p2) ∧ (True → (p2 ∨ p5))) ∧ p3))) → ((True → p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124906411393431470771994418916 : (((((False → p2) ∨ p4) ∨ p1) → ((((p5 → p5) → True) ∧ p4) ∧ (True → ((True ∧ p1) → (True → (p5 ∧ (p3 ∧ p4))))))) → (p3 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → p2) ∨ p4) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63260703181045900341269623480 : ((p5 ∧ ((True ∧ ((p4 ∨ p2) ∧ (p4 ∨ (p4 ∨ True)))) → ((p2 ∧ True) ∧ ((p5 ∨ (False ∨ (p1 ∨ (False → False)))) ∧ (p2 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802739207121846259817547805054 : (((p2 → (p2 → (((True ∨ (p2 ∨ p4)) → ((p3 → p3) ∧ (((p3 → (p2 → p4)) ∧ (p2 ∨ (p3 → False))) ∨ (p5 ∨ p1)))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67352907309645841735309198156 : ((p1 → ((p5 ∧ ((p4 ∨ p2) ∧ (False ∧ (p3 ∧ ((False ∧ (((p3 → (p4 ∨ p2)) ∧ p3) → True)) ∧ ((p4 → p5) ∨ p2)))))) ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257823279803373179456039604568 : ((p3 ∨ p5) → (((True → p3) ∧ p5) → (p4 ∨ ((p1 → p4) → (p1 ∨ ((p2 ∧ (p5 → p1)) ∨ (((p5 ∧ p1) ∧ (p1 ∧ p4)) → p1))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h18.left
    let h22 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112530141220562591021004761121 : ((((((p2 ∨ (((p3 ∨ p5) ∧ p2) ∨ (((p3 → True) → False) → False))) ∨ (p1 ∧ (False ∨ p1))) → (p1 ∧ p3)) → p3) → p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713242055207295400491193084470 : ((((p3 ∨ (((p2 → p5) ∧ p5) → p1)) ∨ (True → (True ∧ (((p3 ∨ ((((p5 ∨ (False ∧ p5)) → p2) ∨ True) → p4)) ∨ True) ∨ p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354844753322989361865366212616 : (p5 → (((p2 ∧ p5) ∨ (True → ((((p3 → p2) ∨ (False ∨ p1)) → (True ∧ ((p2 ∧ ((p4 ∨ p3) → p3)) ∨ (True → True)))) ∨ p4))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42905619935667531406831032082 : (((p3 → ((True ∧ False) ∨ ((p5 → ((p4 ∧ ((False ∨ p1) ∧ True)) ∧ p2)) ∧ ((True ∨ p3) ∧ (p1 ∧ ((True ∨ p2) → p1)))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44842072851138653535245318203 : (((((p4 → p5) ∨ True) ∨ (False ∨ (((p4 ∧ ((p1 ∨ (False → ((p5 ∧ p2) ∨ p1))) ∧ True)) ∨ (p1 → (p4 ∧ p2))) ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602229787182266842836716469088 : ((((p5 ∧ (p5 ∨ ((((p4 ∨ (p5 ∧ (p5 ∧ p2))) ∨ p4) ∧ (p5 ∧ (((p3 ∨ p5) ∨ p5) ∨ False))) ∨ ((True ∨ p4) ∧ p3)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191390571649655246697452903050 : (((True ∧ True) → (((p2 → (True ∨ False)) ∨ p3) ∧ p4)) ∨ ((((p2 → (p4 ∧ ((p5 → True) ∨ True))) → p3) ∧ (p5 ∧ True)) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124490773663119809887744513194 : ((((True ∧ (p2 ∧ (p2 → p5))) ∨ p5) ∧ (True ∧ ((p4 ∧ (((p5 ∧ True) ∨ (p2 ∨ True)) ∨ ((p1 ∧ False) → True))) ∧ p3))) → (p5 ∨ False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h21 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h22 := h8 h21
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h25 := h8 h24
          -- One of the premise coincides with the conclusion.
          exact h25
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h27 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h28 := h8 h27
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h42 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
    case inr h43 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54349007314798209635384990416 : (((p1 ∨ ((False → (p5 ∧ (False → True))) → p2)) ∧ ((p1 ∨ ((p5 ∨ ((p4 → p5) → ((p2 ∧ (p5 → p4)) ∨ p1))) ∨ True)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233290558890987518363941125935 : ((True ∨ (p1 ∨ p3)) → (((((((p5 ∨ p3) → (((p4 → p1) ∧ True) ∨ (False ∧ True))) → True) ∨ p5) ∧ (p2 ∨ True)) ∧ (p5 ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156788598560425567660233867530 : (((p2 ∧ ((((p3 ∨ (False ∨ p4)) → ((((p5 ∧ p2) → p4) ∨ p1) ∧ p2)) ∨ True) ∨ p4)) ∧ p3) ∨ ((p1 ∨ (p1 ∧ p4)) → (p2 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166179195715016321546690264754 : ((p1 ∧ (((p2 → (p1 ∧ (p4 ∧ ((p5 ∨ False) ∨ (p4 ∧ (p4 ∧ p3)))))) ∨ p3) ∧ p5)) ∨ ((True → p1) → (((p3 → p4) → p3) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247588582149111712558191107496 : ((False ∨ p5) ∨ ((((p3 ∨ ((((p3 ∧ ((((p4 → True) ∧ p4) → p2) → False)) → (p2 ∧ p4)) → (p1 ∧ True)) → False)) ∨ p4) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229713039823094253492514375746 : ((p4 → (p2 ∧ p1)) ∨ ((p3 ∨ (p1 → p1)) ∧ (p1 → ((p5 ∨ (p4 → p5)) ∨ (True ∧ (False ∨ (True ∨ (p1 → (p3 ∨ (p5 → True)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181501518077256859202335399674 : ((p5 ∨ ((p2 → (False ∧ (p5 ∨ p3))) → ((p3 ∧ p4) → (p4 → p2)))) → ((p2 ∨ (((p2 ∧ p4) ∨ p3) ∧ (p2 ∧ p5))) ∨ (True ∨ False))) := by
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
theorem thm_5_vars_191792415571702818621318130820 : ((p2 ∨ ((((True → True) → p2) ∨ (p4 → p1)) ∧ p1)) ∨ (False ∨ (((False ∨ p2) → (p1 ∨ (p5 → (p3 ∧ ((p5 → False) ∧ False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638440969409077064193210202788 : (((((p4 → ((p3 → (p5 ∨ p1)) ∨ True)) ∧ (((((p2 → p5) → p1) → True) ∧ (p4 → True)) → (((p1 → True) ∧ p1) ∧ p3))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57595301494229316712105799329 : ((((False → p4) ∧ p2) → ((p5 → (True ∧ p1)) → (p3 → (p4 ∧ (((p1 ∨ p4) ∧ ((p2 ∧ p2) → (p1 ∧ False))) ∨ (p4 ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137380924146637610700312115309 : ((p3 ∧ (((((p2 ∧ p5) → p5) ∧ p2) ∨ False) ∨ ((True → (p1 ∨ (p1 ∨ (p4 → True)))) ∨ (p3 → (False → p3))))) ∨ ((True ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56666105226033181053932099161 : ((((True → p5) ∧ True) ∧ (((((((p2 ∧ p1) ∨ False) → ((p2 ∨ ((p5 ∧ (p1 ∧ p2)) → p2)) → p5)) ∨ p5) → p5) → p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512978006231958196270194653597 : ((((p5 ∧ p1) ∨ ((p1 ∧ (False → p1)) ∨ (((p5 → p5) ∧ (((p4 ∨ p5) ∧ (((False ∧ True) → (p1 → p1)) → p3)) → p2)) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350934007588980540893454382371 : (p4 → (((True ∨ ((((p5 → p2) → True) ∨ p3) → (((p3 ∧ p4) ∧ (p1 ∨ ((p2 ∧ (p2 ∧ p4)) → p5))) ∨ p5))) → False) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317400258818124371255944245570 : (p4 ∨ (((((p3 ∨ p5) ∧ p3) → False) → (p3 → (p1 ∧ (p5 ∨ ((True ∧ p1) ∧ (((p1 ∧ False) ∨ ((p4 ∧ True) ∨ p5)) ∧ True)))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ p5) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∨ p5) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908401247409818405941892544224 : (((((p1 ∨ (p1 ∧ (((False → (True ∧ (p3 → (p5 ∧ p5)))) ∧ (p2 → p1)) → True))) ∧ p1) ∧ ((p4 ∨ (p4 ∨ (p5 → True))) → False)) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ (p4 ∨ (p5 → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (p4 ∨ (p4 ∨ (p5 → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585814817746140963006502200172 : ((((((p1 → (p5 ∧ ((p3 ∧ True) → (True ∧ (((p5 ∧ (((p4 ∧ p4) → (p2 → True)) → p3)) ∨ p4) → p2))))) → p4) ∧ True) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41298147165443600558885565457 : ((((True ∨ ((((p3 → False) → True) ∧ ((p1 ∧ p4) → (p3 ∨ p5))) ∨ (p4 ∧ (p5 ∧ p4)))) → (p1 ∨ ((p1 ∨ True) → p2))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125250229293003298631955098871 : ((((p3 ∧ p3) ∧ p2) → ((p1 → (((p2 ∧ (p4 ∨ p3)) → (p3 ∨ (True ∧ (p4 → p3)))) ∨ ((p2 ∧ True) → p4))) ∧ p5)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631502223717775549749422915375 : ((((((((p5 → (((p3 ∨ p2) ∨ p4) ∧ ((p4 ∨ (p1 ∨ p5)) → p1))) ∨ (p2 → p3)) → p3) ∧ (p3 ∧ (p3 ∧ p3))) → False) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148954851763670311732387095683 : ((((True → True) ∧ p1) ∧ (((((p3 ∨ p2) ∨ (p2 ∧ p2)) → p3) ∧ True) ∧ (((p2 ∨ p2) ∧ True) → p4))) ∨ ((p2 ∧ p3) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670563904833216536440840288628 : (((((p1 ∨ p2) ∨ (((((((p2 ∧ p5) ∨ ((p1 ∧ p2) ∧ p4)) ∧ False) → p4) → p5) ∨ (p3 → p4)) ∧ p2)) ∨ (p1 ∨ (p1 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134071157106994555994448440327 : ((((((p3 ∨ p1) ∨ (p4 ∧ ((((p4 → True) ∨ p1) ∨ (p4 ∨ (p4 → p1))) ∧ (False → p4)))) → False) → p4) ∨ True) ∨ ((p5 ∨ True) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112120506531388756601371813002 : (((True ∧ ((p5 ∧ (((True ∧ (True → p1)) ∨ p2) ∧ (True → (False ∨ (((False ∧ p3) → False) ∧ (p1 ∧ True)))))) → p4)) ∨ True) ∨ (p2 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



