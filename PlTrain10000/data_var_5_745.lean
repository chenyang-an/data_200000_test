variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205151246294133680682110134150 : (((False ∧ (True ∧ False)) ∧ (p3 ∧ p4)) ∨ ((p3 ∨ ((p3 ∨ True) ∨ ((((p4 ∧ p4) ∨ p1) ∧ p5) ∧ (p4 ∨ p3)))) ∨ (False ∧ (p4 ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_496932017456033310310650509935 : (((((p4 ∧ p1) → p1) ∧ ((p5 ∧ (((p3 ∧ (p2 → p4)) → (p4 → (p2 → (True ∧ p5)))) → p2)) ∨ ((p3 → p3) ∨ (p4 ∧ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232764382066406522870793584637 : ((p2 ∧ (True ∧ True)) → ((((False ∧ ((((p2 ∧ p5) ∧ p2) ∨ p3) → (((p2 → (p1 ∨ True)) → p3) ∧ (True ∧ p4)))) ∨ p4) ∨ False) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622991773010026688298336714212 : ((((p5 ∧ ((True ∨ p4) ∧ (((p4 ∨ (p3 ∧ (True ∨ ((p4 → True) ∧ (False ∨ p3))))) → ((p3 ∨ p3) ∨ p5)) ∨ (True ∨ p5)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306053577956716995433213593805 : (p1 ∨ (((False ∨ p1) → (True → p1)) → (((((p5 ∨ p3) ∧ False) ∧ ((p2 ∧ (True ∧ (p4 → (p2 → True)))) → p4)) ∨ p2) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_877951181867208782871517013727 : ((((((False → False) ∨ p5) → ((p3 → (p2 → (p4 ∨ (((p1 ∧ p2) ∨ True) ∨ (p3 ∧ (p4 → False)))))) ∧ (p2 ∧ p3))) ∧ (p2 ∨ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((False → False) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : ((False → False) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42382661592010887752432339869 : (((p4 ∧ ((((((p4 → p2) ∧ p2) ∧ (p1 ∨ p5)) ∨ p4) → (p3 ∧ ((p3 ∨ p1) → (p5 ∧ p4)))) ∨ (True → (p5 ∧ p3)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263804978588782925915901382683 : (True ∧ (((p4 ∨ p5) ∧ (((p2 ∧ p5) → (p2 ∨ (p5 ∧ True))) → ((p2 → p1) → p5))) ∨ ((p5 ∧ (p3 ∧ (False → (p1 ∧ p2)))) ∨ True))) := by
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
theorem thm_5_vars_43771405598461193671127325636 : ((((p5 ∧ ((p1 ∨ p3) ∨ (((True ∨ (((p2 ∧ ((p2 ∧ p4) ∨ (p1 ∨ True))) → p1) ∨ (False → p4))) ∧ p5) ∧ p1))) → p1) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230321360130652919834746540076 : (((p1 ∨ p5) ∧ p2) → (p4 ∨ (((True → ((False ∨ ((p4 ∧ p5) ∧ ((p1 → ((p3 ∨ False) ∧ (p5 → p5))) ∨ False))) ∨ p3)) ∨ p2) ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192315955778064019886711143295 : (((p3 ∧ ((p4 → True) ∨ (p4 → (p4 ∨ p5)))) ∧ p3) → ((((p2 ∨ p5) ∨ ((p1 → (p1 ∧ (p3 ∨ p3))) → p1)) ∧ (p2 ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112366852320688143266488861944 : ((((((p2 ∧ ((p3 → (((p2 ∧ p5) ∨ p4) → (p4 → True))) ∨ p4)) → ((p4 → False) ∨ (p3 → p3))) → p3) ∧ p4) → p3) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345664527480443549472305889846 : (p3 → ((False ∨ ((p3 ∧ ((((True → p1) ∧ p2) ∧ p2) ∧ ((p2 ∨ p2) ∨ ((((p5 ∧ p2) ∨ False) ∨ (p3 ∧ p5)) → p4)))) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694600997341603841220427087 : ((((p5 ∧ ((p2 ∨ (p4 ∧ True)) ∧ p4)) → ((p3 ∨ p4) → p3)) ∨ (p3 ∨ ((((p1 ∨ p2) ∧ p3) → False) → (p2 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88531098605486195143987498604 : (((p1 ∧ (p2 ∧ (True → p5))) ∨ (((p3 → False) → (p3 → ((((p3 → (((p5 ∧ p4) ∨ p2) ∨ p5)) ∧ p4) ∧ p2) ∨ p1))) → False)) → p5) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 → False) → (p3 → ((((p3 → (((p5 ∧ p4) ∨ p2) ∨ p5)) ∧ p4) ∧ p2) ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h10
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742494318599902920014210759470 : ((((p2 → False) ∨ (((((True ∧ p1) ∧ ((True ∨ p5) → p4)) ∨ p4) ∨ p1) → ((p2 → (p3 ∨ (p1 ∧ False))) ∧ ((p3 → p2) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261374169653511252563478285996 : ((p5 → p1) → ((((p1 ∨ (((p4 → p4) → (((((p1 ∨ (p2 ∧ p4)) ∨ True) ∧ p1) ∧ (p3 → p5)) ∧ p2)) ∧ p3)) ∧ p4) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171546051704291168479972044202 : (((((False ∨ ((p5 ∧ ((p2 → (p1 ∨ False)) ∨ p4)) ∧ p3)) ∧ p4) → False) ∨ p5) ∨ ((p4 ∨ False) ∨ ((p5 ∨ (False → (p3 ∧ True))) ∨ p1))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355787881542690046446955922796 : (p5 → ((((p1 ∧ False) ∨ ((p3 ∨ (((p2 → p1) ∧ p5) ∨ p5)) ∧ ((p3 ∨ p5) ∨ True))) ∨ (p4 → (True ∨ False))) ∧ (p4 ∨ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40965163869321146759689667142 : (((((p1 ∧ ((p2 → (p3 ∧ (p4 ∧ p2))) ∧ False)) ∨ (((p5 ∧ (((p2 → True) → p4) ∧ p4)) ∨ True) → p2)) ∨ (p3 → p2)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312048894988208456640750181077 : (p2 ∨ (p5 ∨ (((False ∨ p3) → (((p1 → (((p5 ∨ p1) → p4) ∧ True)) ∧ (p1 → ((p5 → (True ∨ p4)) ∨ (p2 ∨ False)))) ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354732725735230420243692287220 : (p5 → ((((p3 ∧ (((p3 ∧ ((False ∨ p3) ∨ (((p1 ∧ p4) ∧ p3) ∨ p1))) ∧ p1) ∨ True)) ∨ p4) ∨ ((False ∨ False) → (p2 → p1))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147526530823308680897209436388 : (((True → (((p3 ∨ p4) ∨ p5) → (p2 ∨ (((p4 ∧ p2) ∨ ((False ∨ p3) → p3)) ∧ (p5 ∨ True))))) ∨ p1) ∨ (p3 → (True ∨ (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111669738454998719181542285807 : ((((True → (((False ∧ True) ∨ (p2 ∨ (((p5 ∧ (True ∧ True)) → (p3 ∧ p4)) ∧ ((p3 → False) → False)))) → p1)) ∨ p4) ∨ p4) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327865568346931425979785176062 : (True → (((True → p4) ∧ ((p3 → (((p5 ∧ ((p4 ∧ p5) ∨ (p3 → False))) → p3) ∨ False)) → (p1 ∨ ((p4 ∧ p2) ∨ p2)))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40026219050054564134434598077 : ((((((p3 ∨ (False ∨ (((p5 ∧ (p2 ∧ p4)) → ((False ∨ p3) ∧ (True → p2))) ∨ ((p4 ∧ False) → False)))) ∨ p3) ∧ p2) ∧ p4) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315674540863728879968117315554 : (p3 ∨ ((p5 ∧ p4) ∨ ((((p1 → (p4 ∨ (p4 → ((True → False) → (((p1 → p3) ∧ (p1 ∧ p1)) → p3))))) ∨ (p5 ∨ p1)) ∨ p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246284044269426507391628190098 : ((p4 ∧ p4) ∨ (((True → p1) → p4) ∨ (True ∧ ((p4 → (p5 ∨ p2)) → ((p4 → ((p3 → (p2 ∨ p5)) ∧ ((p5 → True) → p4))) ∨ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257289757237959383177839111831 : ((p2 ∨ p3) → (p1 ∨ ((((p2 ∨ ((True → p5) ∨ p5)) ∧ (p5 → (False ∧ (p4 ∨ True)))) ∨ ((p1 ∨ p3) → True)) ∨ ((p5 ∨ p4) → p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38684844053328108658547484260 : ((((p3 ∨ (True ∧ ((p2 ∨ p2) ∧ p2))) ∧ ((p4 ∧ p4) → ((True ∨ (True ∨ (True → (True → False)))) ∧ (p2 → (p2 ∧ p3))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178027779498392906853910164434 : (((p3 → (p5 ∨ ((p2 ∨ (((p3 ∧ p2) → False) → False)) ∧ p1))) ∨ True) ∨ (((p5 → (p5 ∧ True)) ∨ (p2 ∨ (p3 ∨ p3))) ∧ (p2 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54016764307314552937777578803 : ((((p2 ∨ (((p3 ∧ False) → (p2 → False)) ∧ p3)) → p1) → ((True → ((False → False) → (p5 ∧ p1))) ∨ ((True ∨ (p4 ∨ True)) ∨ p5))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55899408100410211659403720848 : (((p3 ∨ (True ∨ (p3 → p4))) ∧ ((p3 → ((((p3 → (p2 → True)) → p4) ∨ (p1 ∧ p4)) ∨ False)) ∨ ((p4 → (False → p1)) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706125794030789551939804082295 : (((((p5 ∧ True) → (True ∧ (p2 ∧ (True ∧ p2)))) ∧ ((((p2 → p5) ∧ p4) ∨ p5) ∨ ((((p4 ∧ (p3 ∧ False)) ∨ p5) ∧ p1) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157536851692854321648235923916 : ((((((((p2 → True) ∧ (((True ∨ False) ∧ p4) ∧ False)) ∨ p1) ∨ True) → p1) ∨ p2) → (True → p1)) ∨ ((((False ∧ p2) ∧ False) → p1) ∨ p1)) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167196969134523668683015978574 : (((p3 ∧ ((p3 ∧ (p1 ∧ ((True ∨ p3) ∧ (p5 → True)))) ∨ ((True ∧ p4) ∧ p4))) ∨ True) → ((False ∧ ((p1 ∨ p4) ∧ p1)) ∨ (True ∨ p2))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40570912120584462754460922592 : ((((p5 → (((p2 → (p4 ∨ (p3 → (p3 ∨ p5)))) ∨ True) ∧ ((((True → p2) ∨ False) → p4) ∧ (p1 ∨ (True → True))))) ∨ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178029094122209924957269459158 : (((p4 → (((((p1 ∨ p3) ∨ True) ∧ p1) ∧ p3) ∧ (p2 → p4))) ∨ p5) ∨ ((p5 → (p3 ∨ ((False ∧ True) ∧ p3))) → (False → (p3 ∧ p3)))) := by
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
theorem thm_5_vars_344589939601718174748603697446 : (p2 → (p1 → (((False ∨ (((True → True) ∧ (True → (((p3 ∧ p3) ∧ p2) → p2))) ∧ ((p4 ∧ (p2 → (p3 → p4))) ∨ p4))) → p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160884694644098311319444070218 : ((((p2 ∧ (True ∧ p5)) → True) ∨ (((p4 ∧ p4) → p3) ∨ (p3 → ((p1 ∨ p1) ∧ (p2 ∨ p3))))) → (p5 ∨ (p5 ∨ (False → (False ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40361326714722538733826072165 : ((((((((((p2 ∧ p2) ∧ p5) → (p4 → p1)) → p1) → p4) → (p4 ∨ (p4 → ((p4 ∨ (p3 → False)) ∧ p1)))) → p2) ∨ p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302828416473918656999921573177 : (False ∨ (p5 ∨ ((((p5 ∧ p1) ∧ False) ∧ p5) ∨ (True ∨ ((((True ∧ (((False → p2) ∧ False) → (True → p4))) ∧ True) ∧ False) ∨ (p3 → False)))))) := by
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
theorem thm_5_vars_185272467662415547927351288021 : ((p1 ∧ (True → ((p5 ∨ (((p2 → p3) ∧ p2) → p1)) ∨ True))) ∨ ((p4 ∨ ((p1 → True) ∨ p1)) ∨ ((p4 ∧ (p1 ∨ (p1 ∧ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_181298098542707076539856489476 : ((p5 ∧ (((p1 ∨ True) ∧ p4) → (((p1 ∨ False) ∧ p1) ∧ (p4 ∧ p2)))) → (p5 → (((p1 ∧ (False ∨ p4)) ∨ ((p3 ∨ p1) ∨ p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715564155787656609832794610137 : (((((p3 ∧ (p3 → p2)) ∧ True) ∧ (((False ∧ (False ∨ ((True → p4) ∧ p5))) ∧ ((p1 → p5) ∨ p4)) ∨ ((p2 → p4) → (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313822453095006368028939251402 : (p3 ∨ (((p5 → (((p3 ∨ p1) ∨ True) ∧ (p4 ∨ (p5 → ((p5 ∨ False) → (p5 ∨ ((True ∨ p3) ∨ (p1 ∧ False)))))))) ∨ p1) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234187389035464396163098645717 : ((False → (False ∧ True)) → ((((p1 → p1) ∧ p2) → (p3 ∨ False)) ∨ ((((True → ((p2 ∨ p1) ∨ p1)) ∨ ((False ∧ p1) → False)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174677488586882325125590684050 : (((p3 → (False ∧ p4)) ∧ (p5 ∨ ((p3 → (p5 ∧ p3)) → (p4 ∨ (p5 → p2))))) → (((p3 ∧ p3) ∨ (p5 ∨ False)) ∨ (p3 → (p2 ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55925561743183820142542743232 : (((False → (p1 → (p3 ∧ p4))) ∧ ((p1 ∧ (((((p4 ∨ True) → p3) ∧ p4) ∨ (p2 → (p4 → p1))) ∧ (True ∨ p5))) ∨ (p5 ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118827627531566801692775379561 : ((True → ((True ∨ (p3 ∨ (((p2 ∨ (False ∨ (p1 → ((p5 ∨ (False ∧ (p3 ∨ p4))) ∧ p5)))) → (True → p5)) ∧ True))) → p5)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84077457727781454349270042600 : ((((p1 ∨ ((((True ∨ p5) → False) ∧ p3) → True)) → ((True ∨ (True → p4)) ∧ p1)) ∧ ((p2 ∧ (p1 → False)) ∨ (p1 ∧ (p2 ∨ p2)))) → p1) := by
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
    have h7 : (p1 ∨ ((((True ∨ p5) → False) ∧ p3) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40096437998016275980491604342 : (((((True → ((((p4 ∨ p3) ∨ ((True → (((p2 → (True → p1)) → (p3 → p1)) ∨ True)) ∧ p5)) ∧ True) ∨ False)) → p4) ∧ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61428177620461626771659367659 : ((p1 ∧ ((((p1 → ((False ∧ (p5 ∨ False)) ∨ (p3 ∧ p3))) ∧ p1) ∧ (p1 ∧ ((p2 ∧ (False → (p5 ∨ p4))) → (p1 ∧ p1)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65897295009583926950519046547 : ((p4 ∨ (False ∧ (((p4 ∧ p3) ∨ False) ∧ ((((True ∧ p2) ∨ (((p3 ∧ (p4 ∧ p4)) ∨ ((p2 → p3) → p5)) → p5)) ∧ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760588700259687400577183049916 : (((p2 ∧ (p3 ∧ (p4 ∧ (p4 ∨ ((((p5 → (p1 ∨ (False ∧ ((p2 ∧ (p2 ∨ True)) ∧ p4)))) ∧ p5) ∨ p4) ∨ (True → (p3 → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114585598719018831911635834575 : (((((False → p2) ∧ p1) ∧ (((p2 → (p5 ∨ (p5 → p2))) ∧ (p5 ∨ False)) ∧ p3)) ∧ ((p2 ∨ (True ∧ (p5 → True))) → p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646378202267842044072479331890 : ((((False → (False → (((p1 ∧ (p1 → p3)) ∧ True) → ((p2 → ((p1 → ((p3 → p5) ∨ p2)) ∧ ((p2 → p1) ∧ True))) ∧ p5)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38130534693387769493501772607 : (((((p4 ∧ (p2 ∧ p2)) ∨ (((p1 ∨ p2) ∨ (((p1 ∨ ((p2 ∧ p1) ∨ p3)) → p1) ∨ True)) ∨ True)) ∧ ((False ∨ p3) → p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749772655059115883996459269646 : (((True ∧ ((((p3 → True) ∨ p5) → (p1 ∧ ((p4 ∧ (True ∧ p1)) ∨ (((p3 ∨ p3) ∨ ((p5 ∧ True) → (p2 → p1))) ∨ p4)))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306141985370117284034186641755 : (p1 ∨ (((p2 ∧ False) ∧ p5) ∨ ((p2 → ((False ∧ p2) ∧ p5)) ∨ (((False ∨ ((p5 ∧ p5) ∧ (True ∧ (False ∨ (p1 ∨ p4))))) → True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113716312793722668262076140158 : ((((p4 → (False → (((False ∨ (True → p2)) → (True ∨ p4)) → ((p3 ∧ (True ∧ p3)) ∧ False)))) ∨ (False ∨ p2)) → (False ∧ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234125986173435391658879281527 : ((True → (p3 ∨ False)) → (((((p5 ∨ (((((p2 ∨ ((False ∧ p2) → (p1 ∨ p1))) ∧ True) ∨ False) ∨ p5) ∧ p1)) ∨ p3) ∧ p4) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h17 =>
              -- One of the premise coincides with the conclusion.
              exact h4
            case inr h18 =>
              -- One of the premise coincides with the conclusion.
              exact h4
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196899829528932776413896176595 : (((p4 → ((p5 ∧ p3) ∨ (False ∧ p1))) ∧ p1) ∨ ((((((p4 → p5) ∨ p3) → p5) ∨ False) ∧ (p3 → p1)) ∨ (p4 ∨ ((p5 ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_175845444604531669879869353794 : ((((((((False ∨ True) ∧ False) ∧ p5) ∨ p4) ∨ p2) ∧ (p3 ∨ p3)) ∨ True) ∧ (((p2 ∨ False) → True) ∧ ((p2 → (p1 ∨ p2)) ∨ (p3 → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165700275980834497196435064689 : (((p5 → (p3 ∨ (False ∧ (p1 ∨ p5)))) → ((p2 → p4) → ((p3 ∨ (p5 ∨ p2)) → p4))) ∨ ((False ∨ p1) ∨ (False ∨ ((p2 ∨ True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693705618811545657459874202646 : ((((((p3 ∨ True) → (p5 ∨ ((False ∨ p4) ∨ (p2 ∨ (p4 ∨ p3))))) ∨ True) ∨ (p5 → (p2 ∨ ((((False → False) ∨ True) ∧ p1) → p1)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_49418384869908005632589646178 : ((((True → ((True ∨ (((True → (True ∧ ((p5 → p4) → False))) ∧ ((p3 ∨ False) ∨ p3)) ∨ False)) → p2)) ∧ True) → (True → (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148171027543257540664733277553 : (((((p1 ∧ True) ∨ ((True ∧ (p5 → True)) ∨ (((p5 ∨ False) → False) ∨ p3))) ∨ p2) ∧ ((p5 ∨ p4) ∧ p4)) ∨ (p5 ∨ ((p5 ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_113610571205333073386244343766 : (((p4 ∨ ((((p1 ∨ ((p4 ∧ ((True → (True ∨ p4)) ∧ (p2 → True))) ∨ p3)) ∧ (p1 → True)) → p2) ∧ p4)) ∨ (False → False)) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313983637201114286815496982164 : (p3 ∨ (((p1 ∧ ((False ∧ p5) → (p2 ∧ p4))) ∨ ((p1 ∨ (((p1 ∨ (((p1 ∨ p2) ∨ p3) ∨ p3)) ∨ p2) → False)) → p2)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216573502998166237467825897657 : ((((p1 ∨ p1) ∧ True) ∧ p2) → (((p5 ∨ p5) → (False ∨ (p1 ∧ p4))) ∨ (False ∨ (False → ((p2 ∧ ((p1 → p2) ∧ (p3 ∨ p2))) ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53863983091325323252038420766 : ((((False → (p5 ∧ p2)) → (((p2 → p3) ∧ p4) → p1)) ∨ (True ∧ ((p4 ∧ p3) ∨ (((True ∨ (p3 ∧ p1)) → (p1 ∨ True)) ∨ p2)))) ∨ p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200810923341683409684512080216 : ((p5 ∧ (((p5 → False) ∧ p5) → (p5 ∧ p4))) → ((False ∨ (p1 → ((((p5 ∨ p4) ∧ ((True → p1) → p1)) ∧ p3) ∨ p2))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615894986150831975740210124591 : (((((p2 ∧ (p4 ∧ ((p2 → (p3 ∧ (True ∧ ((p2 ∨ p3) ∨ p4)))) ∧ True))) ∨ ((((p3 ∧ p2) ∨ p4) ∧ p1) ∨ (False → p5))) ∨ p1) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55475748541685332082798036034 : (((((p3 ∨ False) ∧ p4) ∨ (p4 ∨ p1)) → ((((((p2 → False) ∧ (False ∧ (p1 ∧ (p3 → p3)))) → p1) ∨ False) ∧ (p5 ∧ False)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191918407945072536556843646056 : ((p5 ∨ (p1 → ((p2 ∨ p3) ∧ (False ∨ (p5 ∧ True))))) ∨ ((p2 → ((p1 ∧ (True → (False ∧ p5))) → (p2 ∨ p2))) → (True ∧ (p4 → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173384872257335719732441899815 : ((p4 → ((((p5 ∨ (p4 ∨ p3)) ∨ True) ∧ ((False → False) ∧ p5)) ∨ (p3 → p5))) ∨ ((p3 ∨ (True ∨ (p2 ∧ False))) ∨ ((True ∨ p1) ∧ p3))) := by
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
theorem thm_5_vars_327853582642645872459777160480 : (True → ((((p5 ∨ (False ∨ True)) ∨ (p4 ∨ p5)) → (p5 ∨ ((p3 ∧ (((p4 → p3) → False) ∨ False)) ∧ (p4 ∧ (p1 → p5))))) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48299359932340494802666676093 : (((True ∨ (((False → p5) ∧ (True ∧ (p4 ∨ ((((p2 ∨ (True ∧ p1)) → p5) ∨ (False ∧ p3)) → (p4 ∧ p3))))) ∧ True)) → (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44859690689483740916004565469 : ((((p1 ∨ (p4 ∨ p2)) ∨ ((p1 ∧ ((p5 ∨ ((p4 → (False → p5)) ∨ (p1 ∧ (p2 ∧ ((p4 → p4) ∨ p4))))) ∧ p1)) → True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300242173252375148440671137819 : (False ∨ ((((p4 ∨ p4) → p5) → (((p5 ∧ (p5 ∨ p5)) → ((((p3 ∨ (p5 ∧ p5)) → False) → p5) ∨ True)) ∧ (p3 → p5))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219132242690555382780686184237 : ((True ∨ (False ∨ (p2 → p2))) → (((((p4 ∧ False) → (((p2 ∨ p2) ∧ p5) ∨ (p2 ∨ p4))) → p5) → (p3 ∨ ((p2 ∨ False) ∧ p5))) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319653280334032510261756871070 : (p4 ∨ ((p2 ∨ (p2 ∨ (((True ∨ p4) → False) ∧ p1))) ∨ ((True ∨ (p1 ∨ (((p1 ∧ (False → ((p4 ∧ p5) ∨ p3))) ∨ False) ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753414774724081567735180556195 : (((False ∧ (((((False → (True ∧ p2)) ∧ ((p4 → p1) ∨ ((p5 ∧ p3) → (p2 ∨ False)))) → p5) ∨ (p1 ∨ p5)) ∨ (p5 ∨ (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480666345547267920839603104587 : (((((p1 ∨ ((p5 → (p1 ∨ p3)) ∨ False)) → p5) ∨ ((p1 → ((p4 ∧ True) → ((p5 ∨ p2) ∨ (p1 ∨ ((False → p1) ∧ p2))))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249120089651964694856125137512 : ((p4 ∨ p2) ∨ (((False ∨ p2) ∨ (((p1 ∧ (p2 ∧ (p5 ∧ (p1 ∨ (p5 ∧ True))))) → (((True → True) → False) ∧ p1)) ∨ p2)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39319276972169202706001531857 : (((p2 ∧ (((True ∧ p2) ∨ (((True ∧ p4) ∨ ((((p1 ∨ p2) ∧ (p2 ∨ ((p3 ∧ False) → p1))) → False) → p2)) ∨ p1)) ∨ p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347026510611081620045771958739 : (p3 → ((p1 ∨ ((True → p1) → ((p3 ∨ True) ∧ (True → (((False → True) → p4) ∧ p1))))) ∨ (p3 ∨ (p4 ∧ (((p3 ∨ p2) → False) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713235885732977217991264144687 : ((((p3 ∨ ((p5 ∧ (p4 ∨ p3)) ∧ p2)) ∨ (False → (True ∧ (p3 → (p5 → (((p3 ∧ (p1 ∨ (p2 ∧ p2))) ∨ p5) ∧ (p2 → False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14566025352953454531395246905 : (((((p5 ∨ False) ∧ (((p5 ∨ p4) → ((False ∨ (True ∨ False)) → p4)) ∧ (p1 ∧ (p1 → ((p4 ∧ False) ∨ False))))) ∨ True) ∨ (True ∧ True)) ∧ True) := by
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
theorem thm_5_vars_177786459415356953942803521688 : (((p5 ∧ (False ∧ ((p5 → (((p3 ∧ p5) → False) ∧ p5)) ∨ p4))) ∧ p5) ∨ (True → (p5 ∨ (((True ∨ (p4 ∧ False)) ∧ (p3 ∨ False)) ∨ True)))) := by
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
theorem thm_5_vars_115857326156273877846766338341 : (((True → ((p2 ∨ p3) ∧ p3)) ∧ ((((p4 ∧ ((p1 → (p1 ∨ False)) → (False ∧ p5))) ∨ p2) ∨ p3) ∧ (p4 ∨ (False ∧ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44317011855822402404184315825 : (((((p5 ∧ (((p1 ∨ True) → p5) ∧ (p4 → p2))) → ((p4 → (p2 ∨ p4)) → True)) ∨ ((False ∧ p5) ∧ ((p3 ∧ True) → p1))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111281030137539708082519974955 : ((((p3 ∨ p1) → (p5 ∧ ((((True → (p4 ∧ p3)) ∧ ((p5 ∨ (((p2 → p3) ∨ p3) → p3)) ∨ p3)) ∨ p1) ∨ False))) ∧ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346366887468058664119336890109 : (p3 → ((False ∧ ((True ∧ ((False ∧ (False ∨ (p4 → (p3 ∨ (p4 → p5))))) ∨ (p2 ∧ (True ∨ ((False ∨ p5) ∧ True))))) → p4)) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233237530651798749803547342858 : ((True ∨ (True ∧ False)) → ((((p4 → (p1 ∨ p3)) → (p1 ∨ (((True → p4) → (p3 ∨ (p3 ∧ ((False → p3) ∨ True)))) → False))) ∨ True) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193384365226159787509123668063 : (((True ∧ p4) ∧ (p3 ∨ (p3 → (False ∧ (p1 ∨ p4))))) → (p4 → (((p1 → (p5 ∨ p3)) → p5) ∨ (p1 ∨ (((True ∨ p5) ∨ True) ∨ p3))))) := by
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
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
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
theorem thm_5_vars_692457125694822184581151185408 : ((((((True → p5) ∧ (((p4 ∧ p4) → False) → (True → False))) ∧ (False ∨ p2)) ∧ ((True ∨ True) ∧ (True ∧ (p1 ∧ ((False ∨ p5) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116326585959770813696351794224 : ((((False ∨ True) ∧ p4) → (p2 → ((False ∧ (p1 ∧ (((p3 ∨ (False ∨ p1)) ∨ (True ∨ (p5 ∨ p2))) ∨ True))) ∨ (p5 ∨ p4)))) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149470492283066615121053350626 : ((False ∧ ((p3 ∧ True) → (((p1 ∧ (p5 → p4)) ∨ False) ∨ ((p1 ∨ (p2 ∨ p2)) ∨ ((p2 ∧ p5) ∧ True))))) ∨ ((False ∧ (p4 → p2)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



