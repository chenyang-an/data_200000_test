variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117299299403662315166158374529 : ((False ∧ ((((p4 ∧ p3) ∨ (p3 ∧ p5)) ∧ ((False → (p3 → ((p4 → (False ∧ p5)) ∧ p4))) → (p1 ∨ False))) ∨ (p2 ∧ p3))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114160983583379218463091648594 : ((((((((p4 ∧ True) → ((True ∨ (True → p5)) → True)) → p5) → (True ∧ p1)) → (True ∧ False)) → p2) → ((p5 ∨ p2) → p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48987022172815220623035466133 : (((((p5 → (p5 → p1)) → (((p5 → (((False ∨ True) ∧ ((True → True) → p5)) → p4)) ∧ p3) → p2)) ∨ False) ∨ (p3 ∧ (p3 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164471276922836067447520841794 : ((((((False ∧ (True ∨ p1)) → (((p5 → p2) ∧ p2) ∨ p5)) → (p4 ∨ p2)) ∨ True) ∧ p2) ∨ ((((p1 ∧ p4) ∧ p5) → (p5 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321011638338178780657735309540 : (p4 ∨ (False ∨ ((p4 ∨ (((p5 ∧ True) ∨ (((p3 → p4) ∨ True) ∨ True)) → p4)) ∨ ((p2 ∨ (((p3 ∧ True) → p1) ∨ (p5 ∨ p4))) → True)))) := by
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
theorem thm_5_vars_149904274993731748722503820654 : ((p2 ∨ (p4 → ((p1 → (((p3 ∨ p3) ∧ p1) ∧ (p3 ∨ ((p3 ∨ (True ∨ (True → p2))) ∨ True)))) → p3))) ∨ (((p2 → p2) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255681988501625330080456209564 : ((p5 ∧ p5) → ((((p1 ∧ ((((True → (p4 ∧ (p5 → (p3 → False)))) ∧ p2) ∧ p2) → p1)) → (p2 ∧ p2)) ∨ p3) ∨ (p4 ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198233630998559858467618343874 : ((True ∧ ((p1 ∧ p1) ∧ (p4 ∧ (p1 → p1)))) ∨ ((p4 ∧ (p5 ∧ ((p3 ∧ p5) ∨ (p2 → (((p2 → p3) ∨ False) → True))))) → (p1 ∨ p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45981552100188917709203474943 : (((((((p4 ∨ (False ∨ p2)) ∧ ((p2 ∧ (p1 → (p1 ∧ (p5 ∧ p3)))) → ((p4 ∨ True) ∧ p2))) ∨ False) ∨ p5) ∧ p4) ∧ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1095699236591294506326831741 : ((((((p3 → ((p3 ∨ (True → p2)) → ((p5 ∨ p2) → False))) → True) ∨ p1) → False) ∧ ((p4 → False) ∨ (p3 ∧ (p2 ∨ p4)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p3 → ((p3 ∨ (True → p2)) → ((p5 ∨ p2) → False))) → True) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (((p3 → ((p3 ∨ (True → p2)) → ((p5 ∨ p2) → False))) → True) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (((p3 → ((p3 ∨ (True → p2)) → ((p5 ∨ p2) → False))) → True) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113347514722301058112061963850 : (((False ∧ (p3 ∨ ((p4 ∨ p1) ∨ (True ∧ ((p5 → p3) → ((p4 ∧ ((p2 ∧ p3) ∨ p4)) → (p4 → p1))))))) ∧ (p2 ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213818790006598163505474231670 : (((p4 ∧ (p2 ∧ False)) ∨ p3) ∨ (p5 → (((p5 ∧ (p5 → p5)) ∧ ((True → (((False ∧ ((p4 → True) → True)) ∨ True) ∨ p2)) ∨ False)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41931675236427532090638753870 : ((((p5 ∨ (p4 ∨ True)) → ((p4 ∧ (p5 ∨ (p5 ∧ (((False ∨ p1) ∧ True) → (p2 ∨ p4))))) ∨ ((False ∧ p5) → (p2 → p4)))) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207125610935924173958790814684 : (((p4 ∨ (p3 → (True → p3))) ∧ p5) → ((p1 ∧ (((((False ∨ p1) ∨ False) → (p4 ∧ False)) ∨ False) → ((True → (p3 ∧ p2)) ∧ p4))) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323979261834616239687548273464 : (p5 ∨ ((((((False → ((True → (False → False)) → p1)) → True) → p1) ∨ p4) ∧ p5) ∨ (p5 → ((p1 ∧ p2) ∨ ((False → (p2 → p5)) ∨ False))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198028860586787228976170785380 : (((True ∧ False) ∨ ((p5 ∨ p4) → (p1 ∨ p3))) ∨ (((((((False ∧ (p5 ∨ p2)) → p1) ∨ False) → p3) → True) ∨ p4) ∨ ((p2 → p3) ∧ p4))) := by
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
theorem thm_5_vars_157542971644776984187839118864 : (((((((p3 → False) → ((True ∧ (True → p3)) ∧ p3)) ∨ (p2 ∧ p2)) ∧ p1) → True) → (True ∧ p2)) ∨ (True ∨ ((p3 ∨ p3) ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43689231915671725644116121476 : (((((p4 ∨ (p3 → (p3 → (((False ∧ True) ∧ p3) ∧ p3)))) → (((p1 ∨ ((p5 ∨ p2) ∧ (False ∧ p1))) → False) ∨ p1)) → p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340872861393407405065583955049 : (p2 → ((((True ∧ (p1 ∧ ((p4 → ((p5 ∧ False) → True)) ∧ (True ∧ p2)))) ∧ (True ∧ True)) ∧ (p3 → ((False → (True ∧ p3)) → p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158093884602936446403584547642 : (((((True → False) ∨ p3) ∧ p1) ∧ (p1 ∧ (p4 ∨ (False ∧ (p5 → ((True → False) ∨ (p2 ∧ p3))))))) ∨ ((p2 → ((p3 ∨ p2) ∧ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14939397519065864955183384948 : ((((True ∨ (p4 → p1)) ∧ (((((p4 ∧ p1) → (p2 ∧ (False ∧ False))) ∧ (p2 ∨ p5)) ∨ p2) ∨ (False → (p5 ∨ True)))) ∨ (p1 ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352006759604751850318844237617 : (p4 → (((p3 ∧ p4) ∨ (p2 ∨ ((p3 ∨ False) → p5))) ∨ ((False ∨ ((True ∧ (p5 ∧ (p2 ∨ p5))) ∨ (p2 ∧ (p2 ∨ p1)))) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191289064086275802313699235286 : (((p5 ∨ p5) ∧ (((False ∨ (p4 ∨ p3)) ∧ p2) ∧ True)) ∨ (p3 ∨ ((p5 ∧ (p5 → (p4 ∧ (True ∧ (False → p1))))) → (p1 → (True → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693289214016031164684733759696 : ((((p4 ∨ (False → ((((p1 → ((p1 ∧ p5) → p2)) ∧ p3) → p5) ∧ False))) ∧ ((True → (p5 ∧ p3)) → (((True ∧ p4) ∨ p3) ∧ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
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
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200454373398182617170197030896 : (((p1 → True) ∨ (p2 → (p2 ∧ (p3 ∧ p3)))) → (((p4 ∧ p3) ∧ (((((p3 ∧ True) ∧ p3) ∨ p1) ∧ p2) → p5)) → (p2 → (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317731661927597517315749914950 : (p4 ∨ (((((p4 → False) ∧ ((((True ∧ False) → p3) ∧ (p4 ∧ (p1 ∨ ((True ∧ p4) ∨ p4)))) → False)) ∨ p5) ∨ (False → (True → True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669867946544215786507295044428 : (((((True ∧ (p3 ∧ (((p3 ∧ p4) ∨ ((False → True) → False)) ∨ p3))) ∨ ((True → p5) → ((p2 → p1) ∨ p5))) ∨ ((True → p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231269736227864635259746529484 : (((p5 ∨ True) ∨ False) → (((p2 → False) → ((((False ∧ p3) ∧ p2) ∨ p5) ∧ (p2 ∨ p1))) ∨ ((False → (p5 → (p4 ∧ p1))) ∨ (p4 → False)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137516439962799970461691901570 : ((p5 ∧ ((p5 ∧ (False ∨ (True ∨ p2))) → (((p4 ∧ p5) ∧ False) ∨ (p3 → ((((False → p4) ∨ p2) ∨ p3) ∨ p4))))) ∨ ((True ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190362388219059438944446992364 : ((((p3 ∨ p5) ∧ (((p2 ∧ p2) ∧ p1) ∨ True)) ∨ False) ∨ ((((p1 → p2) → (p3 ∨ True)) ∨ p2) ∨ (((p5 ∧ (p3 ∧ False)) → p1) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_134745611513652622205898146944 : ((((p3 ∧ p2) ∨ (False ∨ (((p4 → (p4 → (p1 → True))) → ((p5 → (p4 → p1)) ∧ (p4 ∧ True))) ∨ p5))) → p4) ∨ (False → (p5 ∧ True))) := by
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
theorem thm_5_vars_258895370051102942645832979655 : ((True → p2) → (((p2 → ((p3 → ((True ∨ (p4 → (p5 ∧ p3))) ∧ (((p4 ∧ p5) ∧ (p5 → p1)) ∨ p3))) → p1)) → p1) ∧ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → ((True ∨ (p4 → (p5 ∧ p3))) ∧ (((p4 ∧ p5) ∧ (p5 → p1)) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60361623608832796843636372875 : (((p2 → p5) → (p2 → ((p2 ∨ (p4 → (((((p3 ∧ (False ∧ (((True ∨ p2) ∧ p1) → p5))) → p4) → p3) → p5) → True))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734875723297611551700413838 : ((((p4 ∧ False) ∧ (True ∨ p5)) ∨ (((((False ∧ p4) → ((p3 ∧ p2) ∨ False)) ∧ p3) → (((p5 ∨ p4) → p4) ∧ p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65497938918819194208848309498 : ((p3 ∨ (p5 ∧ ((True → (((p2 ∧ (False ∨ (p3 ∨ ((p4 ∧ p4) ∧ False)))) ∧ True) ∧ (p3 ∨ ((p4 ∨ (p2 → p4)) → p2)))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171456816800054923795372499906 : (((p4 ∧ (p1 ∨ (p1 ∨ ((p2 ∨ (((True → False) ∨ p5) → p1)) → p5)))) ∧ p4) ∨ (True ∨ ((True → False) → ((p4 → (p4 ∨ p1)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164792110841639876135636186837 : ((((True → (p3 ∨ (False ∧ p4))) ∨ ((p5 ∨ p3) → (p1 ∨ (True ∧ (p3 ∧ True))))) ∨ p2) ∨ (((True ∨ p3) ∧ False) → (p2 ∨ (False → p3)))) := by
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
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184314064665413109064192934573 : ((((True → p4) ∧ ((True ∨ (p1 ∧ p3)) ∧ (p1 ∨ p5))) → p5) ∨ ((((True ∧ (((p4 → (p4 ∧ p5)) → p4) ∨ p3)) ∧ p5) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328712958663152751870446602538 : (True → ((p2 ∧ ((p3 ∨ (False ∧ p4)) ∨ (p4 ∨ (False ∧ (p1 ∧ p1))))) ∨ ((p5 ∨ (((p3 → p3) ∧ (True ∧ True)) ∧ False)) ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_49204809456127938700444749817 : (((((p3 ∧ False) ∨ p4) → (p2 ∨ ((False ∨ p1) → ((((p5 ∨ False) ∨ False) ∧ ((p4 → p3) ∧ False)) ∨ True)))) ∨ ((False ∨ p4) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675800619028560894532141027669 : (((((p2 ∧ (((p5 ∨ p2) ∧ (((False ∧ p1) ∨ p1) ∨ True)) → (p2 → p1))) → (p1 ∧ (p1 ∨ p4))) ∧ (p4 → (True ∨ (p4 ∨ p1)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ p2) ∧ (((False ∧ p1) ∨ p1) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p5 ∨ p2) ∧ (((False ∧ p1) ∨ p1) ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177698730903027623011461848580 : (((((p5 → p4) → ((p4 ∧ p2) ∧ (p4 → True))) ∨ (p1 ∨ p3)) ∧ p2) ∨ (((True ∨ (False ∧ ((p1 → p3) → True))) ∨ (True ∨ p4)) ∨ p1)) := by
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
theorem thm_5_vars_656474640472605947849258707585 : (((((p1 → ((p5 ∧ p5) ∧ (p4 ∧ (p4 → (p4 ∨ p4))))) ∨ ((p1 ∨ ((p1 → p3) → ((False ∨ p2) → p2))) → p1)) ∨ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41833830484431919679465970709 : ((((p2 ∧ (True ∨ True)) ∧ ((((((((True ∨ (p4 → p5)) ∨ p2) → p4) ∧ (p4 ∨ (p1 ∧ p1))) → p3) ∨ p2) ∨ p4) ∧ p3)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677873159458584593639595746636 : ((((((p2 ∨ (p4 → ((True → ((p5 → p2) → ((p1 → False) ∧ p1))) ∧ p5))) ∨ True) ∨ (p3 ∧ p2)) ∨ (p2 ∧ (True ∨ (p2 ∧ p2)))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724142853653157533971225738861 : ((((p2 ∧ (p4 ∨ p5)) ∧ ((((((p4 ∨ ((True ∨ (p1 → (p2 ∧ (True → False)))) ∧ p5)) ∨ p1) ∧ (p1 ∨ True)) ∨ p1) ∧ p4) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323491659520939849729778561537 : (p5 ∨ ((((p1 ∨ p5) ∨ (p2 ∧ (((p3 ∧ (((p4 ∨ p4) ∧ p1) → p1)) ∧ p5) → p3))) ∧ (p5 ∧ (True ∧ p4))) ∨ (p5 → (p5 ∨ p5)))) := by
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
theorem thm_5_vars_647857487595883387472878089043 : ((((((((p3 ∨ p4) → p3) ∨ ((((p4 ∧ p3) ∨ False) ∧ p1) ∨ ((True ∧ (False ∧ (p5 ∨ p5))) → p4))) ∨ p2) ∧ True) ∧ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160626770216869693455104221278 : (((((p2 → False) ∨ (p3 → p5)) ∨ (p5 ∧ (p2 → True))) ∨ ((p2 → (p4 ∨ (p2 ∨ True))) ∨ p3)) → (False ∨ (p1 → ((p5 → p3) → p1)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199545458578083421525979027912 : ((((p5 ∧ ((p4 → True) → False)) ∧ p4) → p2) → (p2 ∨ ((p5 → p5) ∨ (((True → (True ∧ False)) ∨ (False → p2)) → ((True ∧ p5) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40886439762640690755981486700 : (((((((True ∧ (p4 ∨ p2)) ∧ (False ∧ p4)) → (p1 ∨ p4)) → (False ∧ (((p2 ∧ p1) ∧ (True ∧ True)) → p2))) ∧ (p5 ∧ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62828147882996160258497388289 : ((p4 ∧ (((((p3 ∨ p3) ∨ p4) ∧ p2) ∧ (p4 → p5)) ∧ (((p1 ∨ (p4 ∨ (p5 ∧ p1))) → p1) ∨ ((p2 ∧ (p4 ∨ p4)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40942685825882479297136621030 : (((((((((p5 ∨ p4) ∧ (p2 ∨ (p1 → p1))) ∨ True) ∨ ((p2 ∧ p3) ∨ p4)) ∧ (p4 ∧ (False ∨ p5))) → p3) ∨ (True ∨ p2)) ∨ p5) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336465267049671565737326972927 : (p1 → ((p1 → ((p2 ∨ ((((p3 ∨ p4) ∨ p5) → p3) → (p3 ∧ p4))) ∧ (p1 ∨ ((p4 → p2) → (p5 ∧ ((p2 ∧ p4) ∨ p1)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315286806310281529557752863757 : (p3 ∨ ((((p1 → p5) ∧ p1) → p3) → (p3 → ((((True ∨ (p2 ∨ (p3 ∨ p2))) ∧ (True ∧ p3)) → ((p1 ∨ True) ∧ (p3 → True))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h5.left
      let h12 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h5.left
        let h19 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94624872825960564492710710218 : ((p3 ∧ (((((p5 → (((((True ∨ (p2 ∧ p4)) ∨ p2) ∧ p2) ∨ ((p2 ∧ p2) → (True → p4))) → p3)) ∧ True) → p1) ∨ True) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 → (((((True ∨ (p2 ∧ p4)) ∨ p2) ∧ p2) ∨ ((p2 ∧ p2) → (True → p4))) → p3)) ∧ True) → p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218315160404744095449472983584 : (((True → True) ∨ (p3 → p1)) → (((False ∨ p3) → p4) ∨ (((((p3 ∨ p4) ∧ (True ∧ p4)) ∧ p2) ∧ True) ∨ (p4 → ((True ∧ p1) → p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156692074321168844354624537235 : ((((((p3 ∨ p1) → False) → (p2 → ((p1 → p4) → (p3 ∧ p2)))) ∧ ((p5 → p4) ∧ p5)) ∧ p1) ∨ (((p1 ∨ True) → (False ∧ False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177876126637461371953252496912 : (((((((p5 ∨ (p4 ∧ (p2 → p4))) ∨ False) ∨ p3) → p2) → p2) ∨ True) ∨ (p1 ∨ ((True ∨ p4) ∨ (((p2 ∧ (p1 → p3)) ∨ p5) ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784405878872190623016772189904 : (((p3 ∨ (p4 ∧ ((p3 ∨ (((p2 ∨ False) ∧ p3) ∨ ((((True ∧ p2) ∨ (p1 → ((p5 ∧ p4) → (p2 ∨ True)))) → p5) ∧ p4))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327795918454184894308748853210 : (True → (((p1 ∧ ((((p3 ∧ (p1 → True)) ∨ ((p5 → (p3 ∨ (True ∧ p3))) ∨ ((p4 → p2) ∧ p2))) ∨ p1) ∨ p1)) ∧ p2) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347839676385999080883959695654 : (p3 → (((True ∨ False) → p5) → ((((True → (True ∧ (p5 → (False → (p1 → False))))) → ((((p4 ∨ p4) ∧ p5) → p2) ∨ p3)) → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (True ∧ (p5 → (False → (p1 → False))))) → ((((p4 ∨ p4) ∧ p5) → p2) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98588365745846876806867573164 : ((p5 ∨ ((True ∧ (p4 → (p4 ∨ ((p2 → p5) → (p1 ∧ p2))))) → (((p3 ∨ p5) ∨ ((((p4 ∧ p5) → p2) → p1) → p5)) ∧ False))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∧ (p4 → (p4 ∨ ((p2 → p5) → (p1 ∧ p2))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136727702840737279838225621880 : (((p5 ∧ p1) ∧ ((((p1 ∧ p3) ∨ (p4 ∨ p1)) ∧ ((p5 ∧ (False → (p1 ∨ p5))) → (True ∧ (p3 ∨ p5)))) ∨ p1)) ∨ ((False ∧ p5) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48737610452515730241346107922 : ((((p3 ∧ (True ∨ p2)) ∨ (p3 → (True → ((p5 ∨ (((p1 → False) ∨ ((p5 ∨ False) → p1)) → False)) ∧ True)))) ∧ (p1 → (p5 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252551874748718958468149727262 : ((p5 → p2) ∨ (False ∨ ((p4 ∨ (p3 ∧ ((((p3 ∧ p5) ∧ ((True → p1) → (p2 → (p2 → True)))) → p2) → ((p2 ∨ False) ∨ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62931597953427230508011785205 : ((p4 ∧ (p2 ∧ ((p4 ∨ (((p1 ∧ (True ∧ ((p1 ∧ (False ∨ (p1 ∨ (p5 ∧ True)))) ∧ p2))) ∨ p4) ∨ True)) ∨ (p2 ∧ (False ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137764640664409815083378606724 : ((p2 ∨ ((((p4 → ((False ∧ (False ∧ True)) → ((p5 → p2) → True))) ∨ (True ∧ (True ∨ p1))) ∨ p5) → (p2 → False))) ∨ ((p4 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684115635609602431042598823830 : (((((((False ∧ p3) → p3) → ((p2 ∨ p2) ∨ ((p3 ∨ (p5 ∧ True)) ∧ False))) ∧ (p5 ∧ True)) ∨ ((p2 ∨ ((p4 ∨ p1) → p4)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148357626040368036731720467283 : (((p1 ∨ ((True → ((p5 → (p2 → p3)) → ((p2 ∨ True) ∧ p4))) ∧ p3)) ∧ (((False → False) → p3) → p2)) ∨ ((True ∨ p5) ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52173715455694616146479824358 : ((((p3 ∨ ((p5 ∨ p2) ∧ (True ∧ p5))) ∧ ((((p1 → True) ∨ p4) ∨ p2) ∧ p4)) → (p5 → ((p2 ∧ (p4 ∧ (p5 ∧ p3))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258766060334758443647175280738 : ((True → False) → (((p3 ∨ p2) ∨ ((True ∨ (p1 ∨ p3)) → ((((True ∨ p5) → True) → ((p1 → (p1 → p2)) ∧ (False ∧ False))) → p4))) ∨ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234331077974080946872763149988 : ((p1 → (p4 ∧ p3)) → ((((p2 ∧ p3) ∧ p1) → (True ∧ (p5 ∧ ((False ∧ True) ∧ ((p4 → p5) ∨ False))))) ∨ (p3 → (p5 ∨ (p3 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117836582559069063620802500154 : ((p4 ∧ (p3 ∨ (((p2 → (p1 ∧ (((p1 → (False ∧ (p5 → (p2 → (True ∨ True))))) → p3) ∨ True))) → p4) ∨ (True ∧ p3)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149630886080924589758017227012 : ((p4 ∧ (((p2 ∨ ((((p2 → p2) ∧ p2) → (p5 → (p2 → p1))) ∧ (True ∨ p4))) ∧ (p2 ∧ p2)) ∨ p3)) ∨ ((True ∨ (p3 ∧ p2)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260395598821551826394844063449 : ((p2 → p5) → (p5 → (((((p4 ∨ (p5 → p4)) ∨ (((p2 → p2) → ((True ∧ p1) ∧ p2)) ∧ p2)) ∧ (False → p3)) ∧ (p3 ∧ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47219530813846447130433702192 : (((((p1 → ((False → False) ∨ p4)) → ((p1 ∨ p1) ∨ p4)) → (p5 ∧ ((True → ((p1 ∧ p1) ∧ p4)) → (False ∧ p2)))) ∨ (p2 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318654048613439563733141508607 : (p4 ∨ ((p2 → (((p1 ∨ (True → True)) → (p1 ∨ (p3 ∧ ((p3 ∧ (p4 ∨ p1)) ∨ p4)))) ∧ (p4 ∨ ((True → p3) ∧ p1)))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645229991099747369642061267931 : ((((p3 ∨ (p2 ∧ ((((p1 → ((((p4 ∧ ((p4 → p2) ∨ p3)) ∨ p4) ∧ True) ∧ p4)) ∧ p2) ∨ (True ∧ (p5 ∧ p3))) ∧ p2))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641679847679629301934562337985 : (((((False ∨ p5) → ((p3 → p5) ∨ ((p3 → (p4 ∨ ((False → (p4 ∧ ((False → (p3 ∨ True)) ∧ p2))) ∨ p3))) → (p1 ∧ p2)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45431166053691638079412285684 : (((True ∨ (((p3 ∨ (True ∧ ((((p5 ∨ p3) ∧ p1) → p3) ∨ (p3 → p5)))) ∨ (((p3 ∧ p2) ∧ (p1 → p2)) ∨ p4)) → p2)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776610896114157525459510173065 : (((p1 ∨ ((False ∨ ((p3 ∨ p3) ∧ (p5 ∨ (((((p5 → (p1 → p5)) ∧ (p1 → (p5 → p4))) ∧ p5) ∧ p3) ∧ (p4 ∨ p5))))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194036621359199697471463245685 : ((p5 ∨ ((p1 ∧ (p1 ∨ ((p5 → True) ∧ p4))) ∨ p1)) → ((((True ∨ p2) → (p3 → (((p2 ∨ (p4 ∨ p3)) ∧ True) ∧ p3))) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : ((True ∨ p2) → (p3 → (((p2 ∨ (p4 ∨ p3)) ∧ True) ∧ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- True on the right can always be proven directly.
          apply True.intro
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h11
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h9
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : ((True ∨ p2) → (p3 → (((p2 ∨ (p4 ∨ p3)) ∧ True) ∧ p3))) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h24
          -- True on the right can always be proven directly.
          apply True.intro
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h25 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h22
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h20
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h29 : ((True ∨ p2) → (p3 → (((p2 ∨ (p4 ∨ p3)) ∧ True) ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h30
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        -- True on the right can always be proven directly.
        apply True.intro
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h34 =>
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h35 =>
          -- One of the premise coincides with the conclusion.
          exact h31
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h36 := h2 h29
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330924289308191010344354819538 : (True → (p4 → (((p2 → ((p1 ∨ p4) → p3)) ∨ ((p5 ∨ (False ∧ p1)) → (p4 → p1))) ∨ ((p5 ∧ ((False ∨ p5) ∨ p1)) ∨ (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178339575974231366954867399861 : ((((p4 ∨ p5) ∧ (p4 ∧ ((p4 → False) → (p3 ∨ p4)))) ∨ (p3 → True)) ∨ ((p1 → ((p5 → ((p5 ∧ (p2 → p1)) ∨ False)) ∨ p1)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231865270501866285265726687009 : (((True ∨ False) → True) → (False ∨ ((p1 ∨ (p4 ∧ True)) ∨ ((p4 → p1) ∨ (p4 → ((((p3 ∨ False) → p3) ∨ (True → p3)) ∨ (False ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159586594279727154746073247597 : (((p2 → (((False ∧ ((((p2 ∨ False) ∧ (p3 ∧ (False ∨ p1))) → p2) ∧ p1)) ∧ p5) → p4)) ∧ p5) → ((p4 ∧ (False ∧ (p2 ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_167499035341825979259178666722 : (((((((False ∨ (True ∧ p5)) ∨ (True ∧ True)) ∧ p4) ∧ p5) ∨ (p2 → p3)) ∧ (True ∧ p3)) → ((((p5 → (False ∨ p2)) → p5) → p1) ∨ p3)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793089194582434472077793878573 : (((True → ((p1 ∨ True) → (((((p3 ∧ (True → False)) ∨ p4) ∧ p4) ∨ (p5 → (((p5 ∨ p3) ∧ (p4 ∧ p3)) → p1))) ∧ (True ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308392886312393155724141526837 : (p2 ∨ ((((False ∧ True) ∨ ((((((False ∧ False) → p4) ∨ (p1 ∧ True)) → True) → ((p1 ∧ True) ∧ (False ∧ p3))) ∧ (p5 ∧ p3))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347973883421745505017832992246 : (p3 → ((p1 → p3) ∧ (p1 → ((p4 ∧ ((((((p1 ∧ p3) ∨ (p4 ∨ p3)) ∧ p2) ∨ (p4 ∨ p5)) ∧ p5) ∨ False)) ∨ ((p3 ∧ False) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114657360484838634713043184155 : ((((((True → p3) → p1) → (True ∨ p3)) → (False ∨ ((p2 ∧ True) ∨ (p1 ∧ p4)))) ∨ ((p2 ∨ ((False ∧ p4) → p4)) ∧ True)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134373088060782428148903734386 : (((p2 ∨ (p1 → ((p4 ∧ (p2 ∨ True)) ∨ (((False ∨ True) → (p2 ∨ (False ∧ (p1 ∧ False)))) ∧ (p3 → p5))))) ∨ p5) ∨ (False → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111247672132515721821708064480 : ((((True ∧ False) ∨ (p5 ∨ (((((False → (((False → p2) ∨ p2) → False)) → p2) → p3) → (p1 → (p4 ∧ p2))) ∧ True))) ∧ p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119655611314572036023743448031 : (((((p4 → (((p4 ∧ (False ∨ p4)) ∨ (p5 ∨ (True ∨ (p5 → p4)))) → False)) ∧ ((False → p2) → (p3 → p5))) ∧ p4) ∧ p2) → (p2 → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((p4 ∧ (False ∨ p4)) ∨ (p5 ∨ (True ∨ (p5 → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313148667111751358757576040761 : (p3 ∨ ((((p2 ∧ ((p3 ∨ True) → ((p5 ∨ p5) → (p3 → True)))) → (p2 ∧ p1)) ∨ (((p5 ∨ (p3 ∨ p5)) → (p3 ∨ p2)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326917162253171892038420307762 : (True → ((((((p4 ∨ p1) ∧ (p4 ∨ (p3 ∨ p4))) ∨ (p1 ∧ (p3 ∨ False))) → ((((p5 ∨ (p2 ∨ p1)) ∧ False) → p1) ∨ p3)) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254888973875146722488856686738 : ((p4 ∧ True) → ((((((((((True ∧ (True ∨ p2)) → p4) → p1) ∨ p5) ∨ False) ∨ False) ∧ p2) → True) → (False ∨ (p2 → False))) ∨ (True ∨ p5))) := by
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
theorem thm_5_vars_37555845365563028835042537812 : ((((p1 ∨ (p5 ∧ (((p3 → (False ∧ ((p4 ∧ p1) → (False → ((p2 ∧ (p1 → True)) ∨ p3))))) ∨ (p5 → p2)) → False))) ∨ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722035585225021142590722161297 : ((((p1 → ((p5 ∧ p3) ∨ p4)) → (((p1 → (((p2 ∧ p2) ∨ ((True ∨ False) ∧ ((p5 ∧ p4) ∧ (p4 → True)))) ∨ p5)) ∧ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



