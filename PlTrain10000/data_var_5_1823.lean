variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181259337388626670448245276098 : ((p4 ∧ ((((True ∨ (p1 → p4)) ∨ p1) ∧ (p4 ∨ (p1 ∨ p2))) → p1)) → (((((True ∨ p2) ∨ (p2 → False)) ∧ p1) ∨ (p4 ∧ False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∨ (p1 → p4)) ∨ p1) ∧ (p4 ∨ (p1 ∨ p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356645829746760164740278946484 : (p5 → (((p1 ∨ (p5 ∨ (p4 ∨ (False → False)))) ∧ p1) → ((((False → ((p3 ∧ p5) ∧ p4)) → (p4 ∨ (False ∨ (p1 → p3)))) → p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205010598072387144796573029655 : (((p1 ∨ ((p3 ∨ p3) → p5)) → False) ∨ (((p4 ∧ p5) ∧ (True ∧ False)) → ((((p2 ∨ p1) ∧ p5) → p4) ∨ (True ∨ ((False ∧ p4) ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313335508425097284580587484400 : (p3 ∨ ((p5 ∨ (True → (((p2 → ((p4 ∨ (False ∨ p5)) ∨ False)) ∨ (((True ∧ p2) ∨ True) ∨ p5)) ∧ (p2 ∧ ((p1 ∧ True) → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246462325733547380060316487424 : ((p5 ∧ False) ∨ (((p1 ∨ p4) → ((p3 ∨ p4) → False)) ∨ (p1 → (True ∨ (((p5 ∨ (p1 ∧ (p4 ∨ True))) ∨ (p3 → p1)) ∨ (p4 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187389009483917670806716561751 : ((p4 ∧ ((True ∨ ((False ∧ True) → ((True ∨ p3) → p3))) ∨ p1)) → (((((False ∨ True) ∨ p2) ∧ p3) ∧ ((True → p5) → p1)) ∨ (p3 → p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148054708217518512015294253978 : (((p1 ∨ (p5 → (False ∨ (((p5 ∧ (p2 ∨ False)) ∨ ((p1 ∨ p5) → p5)) → (True ∧ False))))) ∨ (False ∨ p2)) ∨ ((p5 → (True ∧ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63177128571474953821713563769 : ((p5 ∧ (((p1 → (p1 ∨ (p1 → True))) ∨ ((((p3 ∨ False) ∨ ((p3 → False) ∨ True)) ∨ (True ∧ (p1 → True))) ∨ p1)) → (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228459747555138841024316235961 : ((False ∨ (p3 ∨ p2)) ∨ (((p3 ∨ p3) ∧ ((((p3 → (False ∧ True)) → False) ∨ (p4 ∨ False)) → (p3 ∨ False))) → ((p1 ∨ (p1 ∨ True)) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340761041858872038370187362345 : (p2 → (((p1 ∨ ((((p3 → (False ∨ p4)) ∧ False) ∧ (((False ∨ False) ∨ p1) → (p3 ∨ ((p2 ∨ (p3 → p3)) ∨ False)))) ∨ True)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689387495178905367638298781612 : (((((((False ∧ (True ∧ p3)) ∨ (p3 ∨ (False ∨ p5))) → (p4 ∨ p4)) → (p2 ∨ p1)) ∨ (((p4 → (False → p5)) ∨ (p2 → False)) ∨ p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327501854069394250193257181693 : (True → ((((True ∧ True) → False) ∧ (p5 ∨ ((((p5 → (True ∨ (True → False))) ∧ p3) → p1) → (((True → p3) ∨ p4) ∨ (p3 ∧ p2))))) → p2)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723143486426943208800613858859 : (((((p5 ∨ p5) ∨ p4) ∧ (p5 ∧ ((p4 → p2) → (((((False ∧ p3) ∨ p5) → p1) → ((True ∧ p3) → (p5 → (p4 ∧ False)))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173084978601716426091792587845 : ((p1 ∨ (((p5 ∧ p2) ∧ (((p2 → p1) → p2) ∧ (p2 → p5))) ∨ (p3 ∨ p4))) ∨ ((((p5 → (p4 ∨ p2)) ∧ p3) → (p2 → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148013075236261544602083413165 : (((((p2 → p3) ∨ ((p3 → p1) ∧ (((p5 → False) ∧ p2) → False))) ∨ ((p4 ∧ p3) ∨ p4)) ∨ (p4 ∨ True)) ∨ ((p2 → p1) ∧ (p2 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211344270502237502995251567288 : (((p3 ∨ p3) ∨ (p1 ∨ True)) ∧ ((p5 ∧ ((p4 → False) ∧ p4)) ∨ (True → (((False ∨ ((True ∨ p4) ∧ p2)) ∨ (False ∨ (False → p4))) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320004018310753216378773026264 : (p4 ∨ ((p2 → (p4 ∨ True)) ∧ (p3 ∨ (((False ∨ (((p3 ∧ p5) ∨ p5) ∨ (p5 → (p2 ∨ (True ∧ p4))))) ∧ (p1 ∧ p4)) → (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h4.left
        let h12 := h4.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h4.left
        let h15 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h4.left
      let h18 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307253623597535282860783877806 : (p1 ∨ (p2 ∨ (((False ∨ p5) → ((p2 ∧ False) ∨ ((p3 ∨ (False → ((p3 ∨ p4) ∧ (((p5 → p1) → p1) ∧ True)))) ∨ p3))) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_8954536683245090734661862445 : ((((((p2 → (p5 → (p3 → False))) ∧ (p3 → p2)) → (p3 ∨ (False ∧ (p2 ∧ False)))) ∧ (((False → p5) ∨ False) → (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676765648577491397978755909515 : ((((False ∨ (p1 ∨ (((p1 → (((p5 → (True ∧ False)) ∧ False) ∧ True)) ∧ ((p3 → p3) ∧ p2)) → p2))) ∧ (p4 ∨ ((p1 ∨ p4) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65888953463483549183838135941 : ((p4 ∨ (True ∧ ((((((p4 ∨ False) ∧ (p2 ∧ p4)) → (False ∨ True)) → ((p5 → True) ∧ (p2 ∧ (False → (True → p5))))) → p5) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_112380141601406499060492355150 : (((((((True ∧ (True ∨ p3)) ∧ p4) → (((True → ((p2 ∧ True) ∨ p3)) → p3) → p5)) → (True → (p3 ∧ p1))) ∧ p5) → p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51453569906442444094619484541 : (((((((p1 → ((p2 ∧ False) → p3)) ∧ (True ∨ p4)) → p3) ∨ p3) → (p3 ∨ (p2 ∧ p3))) → (((True ∧ (p1 → p5)) → p1) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50899344812588238030109609809 : ((((((p1 ∨ ((((p2 ∨ p4) → p5) ∧ p1) ∧ (p4 ∨ p2))) ∧ p3) ∨ p2) ∧ (p2 ∧ False)) ∧ ((p3 → p5) → (p2 → (p1 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225675465798356390646418486681 : (((p2 → p5) ∧ p1) ∨ ((((((p5 → p4) → False) ∧ True) ∧ (((p5 → (p4 ∧ True)) ∨ (False → p3)) → p1)) ∧ p2) → ((p4 → p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h9 : ((p5 → (p4 ∧ True)) ∨ (False → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h9
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200176318307608879459766561205 : ((((p4 → p4) → p4) ∨ (False ∧ (p2 ∧ p3))) → ((((p1 → p1) ∨ (True ∨ (p2 ∧ True))) → ((False → p4) → (False ∨ p1))) ∨ (False → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41047316651546158161616064573 : ((((((p5 → (p1 → p1)) ∧ p1) → ((p3 → p2) ∧ ((True ∨ (p4 → p3)) → ((p1 ∨ False) → (p5 ∧ p4))))) → (p2 ∧ p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112372541331253735276368073142 : (((((True ∨ ((False ∨ p3) ∨ (((p1 ∨ (p2 ∧ (((p5 → p4) → p1) ∧ p5))) ∨ False) ∧ p3))) ∧ (p5 ∧ p2)) ∧ True) → False) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259399830082319396446338717255 : ((False → p3) → ((((p4 → p2) ∧ p3) ∨ p2) → ((p1 ∧ p3) ∨ (p2 ∨ ((False ∨ (False ∧ ((p5 → False) → p4))) → ((False ∨ False) ∧ p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148234512931649482812435788471 : (((((p3 → ((p4 → p1) → ((p2 → p4) ∨ p4))) ∨ (p1 ∨ p2)) ∨ (False ∨ p3)) ∨ (False → (p2 → p2))) ∨ (p1 → ((p1 ∨ p2) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47249906888855888794698974129 : ((((p3 → (((p1 → p4) ∧ p1) → p1)) ∧ (False ∧ (((p1 ∧ p2) ∧ (p2 ∨ (p2 ∧ p5))) → (p4 ∧ (p3 ∧ p3))))) ∨ (p1 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171450117111789507639064721273 : (((p2 ∧ ((p4 ∧ p4) ∧ ((((p5 ∨ (p4 → p4)) ∨ p2) ∧ p3) ∧ False))) ∧ p2) ∨ ((p4 ∧ p4) → (p4 ∨ (p3 → (True ∨ (p1 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322408952298113375441949765969 : (p5 ∨ ((((((p3 → (p5 ∧ (p5 ∨ False))) → True) ∨ p4) ∧ p1) ∧ ((((p3 ∨ p4) ∨ (p1 ∧ p5)) ∨ p5) → (False ∧ (p3 → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690440693345541785808433671350 : ((((((False ∧ ((p5 ∨ (((p2 ∧ p2) ∧ p5) → (p1 ∨ p2))) → p1)) → p2) ∧ True) → (p3 ∧ ((p5 → (False → (True → p4))) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354756798310707934673558248102 : (p5 → ((((p2 → (p4 ∨ True)) → (((p1 ∨ (p2 ∨ (p4 ∨ p4))) ∧ False) ∧ p2)) ∨ ((((p4 ∧ (p2 ∨ p3)) ∨ False) ∨ False) ∧ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748967651205121387310874263941 : ((((p4 → p3) → (p3 → (((p4 ∨ (False ∨ (True ∧ p4))) ∨ ((p5 ∨ (p3 ∨ p3)) ∨ ((((True → p3) ∧ p1) ∨ p3) ∧ p4))) ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727834741761995499647105261227 : ((((p1 ∨ (p1 ∨ p4)) ∨ (((p3 ∨ ((p1 ∨ p2) ∧ p2)) ∨ (p2 ∧ False)) → (p4 ∨ ((((p2 → p2) → (True → p5)) ∨ p3) ∨ p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209231421527624066504042300486 : ((p5 ∨ (((p4 → p1) → p3) ∨ False)) → (((p2 ∨ ((p2 ∨ ((p1 → p2) ∧ p4)) ∨ (p4 → (((p1 ∨ p2) ∧ p3) → p1)))) ∨ True) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82269419996051391214922584313 : ((((((False ∧ ((((p1 ∨ (p1 ∨ (p4 ∧ False))) ∨ p1) ∧ True) ∧ p4)) → (p4 ∧ p2)) ∨ False) → False) ∧ (((p5 → p4) → p5) → p1)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∧ ((((p1 ∨ (p1 ∨ (p4 ∧ False))) ∨ p1) ∧ True) ∧ p4)) → (p4 ∧ p2)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112809472480299453977449739175 : (((((True → ((p5 ∧ p2) ∨ p5)) → p2) → ((((False ∧ True) ∨ (p1 → p5)) ∧ ((False ∧ p5) → True)) → (p5 ∧ p4))) → p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162366075490096570727720688807 : ((((((p5 ∧ p3) ∨ (((False → p4) → p2) ∨ (p4 ∨ p2))) → (p2 ∨ p4)) → False) ∨ True) ∧ (p2 → (p2 ∨ ((True ∧ False) → (p2 ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710092673692563856360884635424 : (((((p4 → ((p1 → p1) ∨ p1)) ∧ False) ∧ (True ∧ ((p1 → (((True → p2) ∨ (True ∧ p5)) ∨ p4)) → (p1 ∧ (p2 → (p2 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152109484854322843370586016012 : ((((((False → p4) → (p5 → p1)) → p5) ∧ p5) ∧ ((False → True) → (p4 → ((p3 ∧ p1) ∧ (p1 → True))))) → ((False ∨ p4) ∨ (False → p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156784035466203591735391614026 : (((False ∧ (p2 ∨ ((p2 ∧ (p5 ∧ ((p2 ∨ ((True → False) ∧ p2)) ∨ (p5 → p2)))) ∨ p1))) ∧ True) ∨ ((p1 → p1) ∨ (p5 ∧ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66128398144171956070557000607 : ((p5 ∨ (((True ∧ (False → (p3 → ((((((p1 ∧ True) → (p2 ∧ False)) → p4) ∨ p3) ∧ False) ∨ p5)))) → (p2 ∧ p2)) ∧ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665617670967052609933399189610 : (((((((p2 ∧ p3) ∧ p5) ∧ ((p3 → ((True ∨ (p4 ∧ p2)) ∧ ((p5 ∨ (p3 ∧ False)) ∧ p4))) ∧ p3)) ∨ False) ∧ (p3 → (False → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206976194290002279605428362207 : ((((p2 → (False → p5)) → p1) ∧ p5) → (((p3 ∨ p5) → p4) ∨ ((((p2 → p2) → (p3 ∨ p5)) ∧ False) ∨ (p1 ∨ (p5 → (True → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_788153867267589125459018375534 : (((p5 ∨ ((((p1 ∨ (p2 → ((p5 ∧ p2) ∧ True))) ∧ p1) → ((True ∨ (p4 ∧ True)) → (((p3 ∧ p5) ∨ p3) ∨ (True ∨ p3)))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588311754381661197224350453034 : (((((((p1 → p5) → (p3 ∨ True)) ∧ ((True ∨ p2) ∧ ((((True → (p2 → True)) ∨ (True → p5)) ∨ p1) → (p1 ∨ p3)))) ∨ p1) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84636289052060146012972036322 : (((p1 → ((p4 ∧ (p5 → ((p1 ∨ False) ∧ p3))) ∨ ((p1 ∨ (p5 → p5)) → True))) → (((((p1 ∧ p5) ∨ p3) ∨ False) ∨ p2) ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p4 ∧ (p5 → ((p1 ∨ False) ∧ p3))) ∨ ((p1 ∨ (p5 → p5)) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178003298163615353220590708504 : (((p2 ∨ (p1 ∧ ((p3 ∨ p3) ∧ (p1 ∧ (False → (p5 ∧ p2)))))) ∨ True) ∨ (((True ∧ (False ∧ True)) → p5) → (((p3 ∨ p4) ∧ True) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115222906396331620051980742563 : ((((((True ∨ p5) ∨ ((False ∨ p3) ∨ p4)) ∧ False) ∧ p2) ∨ ((((False ∧ (True → p1)) → False) ∧ (False ∧ p4)) ∨ (p2 → p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257870761011328952873716883000 : ((p4 ∨ True) → ((((((((p1 ∨ (p2 ∨ p1)) → p3) ∨ (p3 ∨ p1)) ∧ True) → False) ∨ p5) ∨ (p5 → True)) ∨ ((p3 → p2) → (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51971039749366702038869290419 : ((((p4 → (p4 → False)) ∨ (((p5 ∧ p1) ∨ p3) ∧ (((False → p4) ∧ p2) ∧ False))) ∨ (True ∨ ((p2 ∧ True) → ((p3 → p5) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40324886280940610677053519129 : ((((((p5 ∧ (p5 → ((((((p1 ∨ p1) → (p3 ∨ p3)) → (False ∨ (p3 ∨ p5))) → False) → p1) → False))) ∧ p4) ∨ p2) ∨ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696564087607224266321085870977 : (((((((((p5 ∨ p4) ∧ (p1 ∨ p1)) ∨ p2) ∨ p3) ∨ p5) ∨ True) ∧ ((p2 ∨ False) → ((p4 ∧ p1) → ((False ∨ False) ∨ (True ∧ p1))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232026174988781864286396497403 : (((p3 ∨ False) → p4) → (((((p4 ∨ p4) ∧ ((p5 ∧ True) → (p5 ∧ p1))) → p2) ∨ (True → ((p5 → (False → p5)) → (p4 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205614173034779639922604520883 : (((False ∧ p1) ∨ ((p5 ∧ p2) ∨ p4)) ∨ (((((p4 → ((((p1 ∧ True) → p5) ∧ False) ∨ p2)) → p5) ∧ False) ∨ p3) → (p4 ∨ (True → True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64123201575098900734575045334 : ((False ∨ (((p1 ∨ (False ∨ True)) ∧ p3) ∧ ((((p1 ∧ (True ∧ False)) ∨ (False ∧ (p5 → (True → (False ∧ p2))))) → True) → (p5 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1758789281680917488461675202 : ((((((p2 ∧ p4) ∧ p3) ∨ (((p2 → p4) ∨ (p1 ∧ (p5 → p3))) ∧ (p5 ∧ (True ∨ p3)))) → p2) ∧ p1) ∨ ((p3 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207362929920916650244344768597 : ((((p4 ∨ False) → (False → p3)) ∨ p5) → ((((((p1 ∨ (False ∧ p1)) → ((p3 ∨ p3) → (p5 ∧ False))) ∨ p1) ∧ (True → False)) ∧ True) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h17 := h6 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h20 := h6 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688644237520642663944875237249 : ((((p5 ∨ ((False ∨ p2) ∨ (False → (p4 ∧ ((((p2 ∨ p4) → p5) ∧ p5) ∧ p4))))) ∧ (((False ∨ (p4 → p5)) → p5) ∨ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810533016834443793350167173004 : (((p5 → ((((p3 ∨ p2) ∨ p4) ∧ p3) ∧ ((p1 → ((((p3 → (True → True)) → p3) ∨ ((p1 ∧ p5) → p1)) ∧ False)) ∨ (p5 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647848402717875563099398442982 : (((((((p3 ∨ ((((((False ∨ p1) ∨ p4) ∨ p3) → p1) ∨ p4) → p5)) ∧ ((True ∨ (p2 → p1)) ∧ p3)) ∨ False) ∧ p1) ∧ (p5 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260185842055995539065344701056 : ((p2 → p2) → ((p5 ∧ ((p1 ∨ p3) ∧ ((False → p2) ∧ p1))) ∨ ((((p4 → (False ∧ p3)) ∧ p1) ∨ (p5 → True)) ∨ ((False → p5) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610271224367649028429239711787 : (((((((p2 → True) ∧ (((((p3 → p1) → p1) ∨ p1) ∨ (False ∨ ((p1 ∧ True) ∧ ((False ∨ p3) → p4)))) ∨ p1)) ∨ p5) → p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64482361303159902119369257649 : ((p1 ∨ (((p5 ∨ (p3 ∨ (((p4 → p4) ∧ p4) → False))) ∧ ((((p5 ∧ False) ∨ p2) ∧ p3) → False)) ∨ ((True ∧ False) ∨ (p5 → p5)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4634231768059382888810669516 : (p5 → ((p1 ∨ (((False ∧ (((((p3 ∧ (p5 ∨ False)) ∨ (p3 → False)) ∨ p4) ∨ p3) → False)) ∧ (p5 → False)) ∨ (False ∧ True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720489039208563720135093921560 : (((((p2 ∨ (p2 ∨ p5)) ∨ p2) → ((((p1 ∧ (((p4 → p4) → ((p3 ∨ p4) ∧ p5)) → True)) ∨ p4) → (p3 ∧ (p4 ∧ p3))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614604608781020410725371119991 : (((((p3 ∧ ((((p3 ∧ ((p5 → (True → True)) ∨ (p1 ∧ True))) → True) → (True ∨ p4)) ∨ p5)) ∧ ((p1 → (p3 ∧ False)) → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299420310413102468646087771089 : (False ∨ ((p4 ∧ (True ∧ (((p3 → (p1 ∧ (False ∧ (p1 → (p3 ∨ ((p5 → (p2 ∨ (p3 → p3))) ∨ p2)))))) ∨ (True → False)) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62513983419257327193508009108 : ((p3 ∧ (p3 ∧ (True ∧ ((((p1 ∨ (False ∧ ((((p2 ∧ True) ∨ False) ∧ p4) ∨ ((p4 → (p3 ∧ p3)) ∧ p3)))) ∧ p2) ∧ p2) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156736275690929794303947243713 : (((((p1 ∧ p4) ∧ (p5 ∨ p3)) ∨ ((p5 ∨ p4) → (p5 ∧ (p1 → (p1 ∨ (p2 ∨ p5)))))) ∧ True) ∨ ((p3 ∧ p5) → (p3 → (p4 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82133877113070013327885353946 : (((p1 ∨ (p5 ∨ (p3 → ((p2 ∧ p5) ∨ ((p5 ∨ ((p5 → p5) ∧ (p4 ∨ ((True ∨ p2) ∨ False)))) ∨ p4))))) → (False ∧ (p2 → False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p5 ∨ (p3 → ((p2 ∧ p5) ∨ ((p5 ∨ ((p5 → p5) ∧ (p4 ∨ ((True ∨ p2) ∨ False)))) ∨ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183921409307744412504958492951 : (((p2 ∧ (((((p5 → p4) ∧ True) ∨ False) → p4) → p5)) ∧ False) ∨ (((((p3 ∧ p3) ∨ p1) → True) → True) ∨ ((p3 → p4) ∧ (True ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354569352990528521375424938939 : (p5 → (((((True ∨ (False → False)) → (((p4 → p4) ∧ (p1 ∧ (p2 → (False ∨ (p5 ∧ True))))) ∨ (False ∧ False))) ∧ (p4 → p5)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612796836453708426532680720122 : ((((((p1 → p3) ∧ (p5 → ((p5 ∧ p4) ∨ (((((p4 ∨ p2) ∨ (p1 → p3)) ∧ True) → p2) ∨ (p2 → True))))) ∨ (p2 ∨ p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258115556508785881332456960715 : ((p4 ∨ p3) → ((((True → p5) → False) ∧ (((False → (False → False)) ∧ ((True ∨ False) ∧ p2)) ∧ p1)) ∨ (((p2 → False) → (False → p1)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38239636583328171826424445891 : ((((((p4 ∨ (False ∨ p1)) → ((((True ∧ True) ∧ p4) → (p1 → (False ∨ p5))) ∧ True)) ∨ p2) ∧ (((p1 → p2) ∨ False) → p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_847166463924050407690639391 : ((p1 ∨ (((((p5 ∨ p3) → False) ∧ (p4 ∧ p2)) ∨ True) ∧ (False → ((False → ((p4 ∨ (p5 ∧ p3)) → (p4 → p4))) → p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323245036489062646204316677141 : (p5 ∨ (((p2 ∨ p4) ∨ ((p2 ∧ ((True → (((False ∨ True) ∧ (((p1 ∧ (p4 → p5)) → True) ∨ p2)) ∧ p1)) ∨ p4)) ∨ p5)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786680526976518137761925931356 : (((p4 ∨ (((p4 ∧ ((p4 ∨ p5) ∨ p4)) ∨ p1) ∨ (False ∧ ((True → p5) → ((p1 ∧ (((p5 ∨ True) → True) ∧ (True ∨ p5))) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683700784513220439173883127530 : (((((False ∨ ((True ∨ p3) → (((False ∧ p3) ∧ (p1 ∧ (True ∨ (False ∧ p1)))) ∧ False))) ∧ p4) ∨ (((p3 → p3) ∧ p2) ∨ (False → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53557880608659563555155499294 : (((((p5 ∧ ((False → (False ∨ p1)) ∨ False)) ∧ p5) ∨ p2) ∧ (((((p2 ∨ p5) ∧ (p1 ∨ (p1 → p3))) ∧ p3) → p3) ∧ (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626718181746889958402693112544 : ((((p5 → ((p3 ∨ ((p5 ∨ True) → (((True ∧ p5) ∧ (p1 ∨ ((p1 ∨ (p1 → p3)) ∨ p3))) ∧ (p2 → (p3 ∨ p4))))) ∨ True)) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200077381359992418650358652931 : ((((True ∧ True) ∨ p2) ∧ ((p4 → p2) ∧ p4)) → (((p1 ∨ True) ∧ (p1 ∧ (p2 ∧ (((p1 → ((p5 ∧ p3) → p5)) → p1) → p3)))) ∨ p2)) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58408502365921180945416953918 : (((p2 ∨ p1) ∧ (((False → p1) ∧ False) ∨ ((((p3 ∧ False) ∨ (p3 ∧ ((False ∧ False) ∨ (True ∨ ((p3 ∨ p2) ∨ False))))) ∧ p1) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231669568483661519705135518025 : (((p1 ∧ False) → p1) → ((((((p3 ∨ (p2 ∨ ((p1 ∨ p3) → ((p2 ∨ p5) ∧ p5)))) ∨ p3) → (p1 ∧ p2)) ∧ p3) ∧ (p2 ∨ False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 ∨ (p2 ∨ ((p1 ∨ p3) → ((p2 ∨ p5) ∧ p5)))) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181247418459454890307225902581 : ((p3 ∧ (p2 ∨ ((False → (((p5 ∨ False) ∧ (p2 → False)) ∧ p5)) ∨ p1))) → ((p5 → ((((p4 → p4) → (p4 → True)) → p3) → p1)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171267250603367403297997526013 : ((p5 → (((p3 → p1) ∨ (((p2 → (False ∧ p1)) ∨ (p4 → True)) ∨ p4)) ∨ True)) ∧ ((True ∨ p4) → ((((False ∨ p4) → p3) ∧ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_42113481964106653177442141847 : ((((p4 ∧ p1) → (True ∧ ((((p4 → (p1 ∧ True)) ∨ p5) ∨ p4) → (p5 ∧ (p5 ∧ ((((p2 → p2) → p5) ∧ p2) ∧ p3)))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54123238804255702727875174176 : (((False ∨ (((p2 ∧ ((p3 ∧ p2) ∨ p5)) ∨ True) → p4)) → ((((p4 ∨ (False → (p1 → p2))) ∧ p5) → (p4 ∧ (p5 ∧ p1))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156733890341745173730594441715 : ((((p4 ∧ (p2 → (p3 → p1))) ∧ ((p2 ∧ ((p1 → (False ∨ p2)) → (p1 ∨ p5))) → p4)) ∧ p1) ∨ ((((True → False) ∧ p1) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134154656191223823209624608884 : ((((p4 ∨ (p1 ∨ (((p5 ∨ True) ∨ p3) ∧ ((p3 ∧ (True ∨ (p3 ∨ p1))) ∨ p3)))) ∨ (p5 ∨ (p4 → p4))) ∨ p1) ∨ ((p4 → False) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56500777312074298384208618556 : (((p2 ∧ ((True ∨ p1) ∨ True)) → (p3 ∨ ((p4 → (((((True ∨ True) ∧ False) ∧ p4) → p1) ∧ (True ∧ (p5 ∧ (False ∧ True))))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244692362317372775135180780153 : ((p1 ∧ True) ∨ ((((p4 ∨ ((((True ∨ True) ∧ (p1 → p5)) ∨ p5) → False)) ∧ (p3 → (p5 ∧ p2))) → p1) ∨ (True ∨ (p2 ∧ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164857146810304485887867721283 : (((p1 ∨ (((((((p2 → False) ∧ (p4 → p2)) → p4) ∧ p3) ∧ False) ∨ False) ∨ p1)) ∨ True) ∨ (p1 → ((p3 ∨ p5) ∧ ((p4 ∨ p3) ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41430705401359362900731446051 : (((((p5 ∨ ((p3 → (((p3 → p2) → True) ∨ p1)) → (p3 ∧ p3))) → True) → (p5 ∨ ((p5 ∧ p2) ∨ ((p4 ∨ p1) ∨ p4)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908704177089930527948395436424 : (((((((False → p1) ∨ (p5 ∧ p3)) → ((p3 ∧ (False → False)) → ((p3 ∨ p4) ∨ False))) → p2) ∧ (((True → p3) ∨ p5) ∧ (False → p4))) → p2) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((False → p1) ∨ (p5 ∧ p3)) → ((p3 ∧ (False → False)) → ((p3 ∨ p4) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : (((False → p1) ∨ (p5 ∧ p3)) → ((p3 ∧ (False → False)) → ((p3 ∨ p4) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h27 := h2 h18
    -- One of the premise coincides with the conclusion.
    exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739532988896174366545925627340 : ((((p5 ∧ p2) ∨ ((True → (((((p4 → (((p3 ∧ p3) ∧ p2) → p3)) → p5) ∨ ((p2 ∨ (p1 ∧ p3)) ∧ p5)) ∨ p1) ∨ p2)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



