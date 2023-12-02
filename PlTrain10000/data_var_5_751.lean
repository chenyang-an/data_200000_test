variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140393040719849130698357049560 : (((True → ((((p4 ∧ p2) → (p2 ∧ p1)) ∧ ((((p4 ∨ p1) → p2) ∧ p2) → p4)) ∧ p4)) ∨ ((p2 → p5) ∧ p4)) → ((p1 → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704450629675660827777744209122 : ((((((p2 ∧ p5) ∧ p5) → (((p3 → p4) ∧ p1) ∨ p2)) → ((False ∨ (p2 → ((p1 ∧ p4) ∨ ((p3 ∧ False) ∨ p3)))) ∨ (False → p5))) ∨ p5) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226932504936477035326361134599 : (((True ∨ p4) → p5) ∨ ((((p5 ∨ False) ∧ (p4 ∨ (((p2 → (p2 ∧ p3)) ∧ p5) ∨ p5))) ∧ (False ∨ (p1 → ((False ∧ p3) ∧ p5)))) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h16
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233320451578949423972863804287 : ((True ∨ (True → p5)) → ((p5 → (p5 ∧ ((((True ∨ ((True ∧ p3) ∧ True)) ∧ (((p4 ∨ False) → p3) → True)) → p3) ∨ False))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256337691516808262996859433562 : ((False ∨ p2) → ((False ∨ (((p2 ∧ ((((p4 ∨ p4) ∨ p5) ∧ True) ∧ p5)) ∧ ((p4 → p1) ∨ (((True ∨ False) → p5) ∧ p4))) ∧ p5)) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640779338682449503413109573494 : (((((False → p5) ∧ (((p1 ∧ (p2 ∨ p4)) ∨ False) ∨ (p3 ∨ (((p1 ∨ (p5 ∨ p5)) → p4) ∧ ((p5 ∨ True) ∧ (p1 ∨ p1)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187502854063737965470078005466 : ((False ∨ (p4 → (p2 → (((p4 → (p3 ∧ p5)) → True) ∧ p4)))) → (((p5 ∧ p5) → p3) ∨ (((p5 ∧ (p1 → p3)) ∧ p2) → (p5 ∧ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238323664469384450116623861564 : ((False ∨ True) ∧ ((True → (((p1 ∧ (p3 ∨ p1)) → p1) ∧ False)) → ((((p4 → p3) ∧ p3) ∧ (True ∨ (p4 ∨ (p4 ∧ p2)))) ∨ (p1 ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651104120641867832218150050438 : ((((((p3 → (p5 → p3)) ∧ p5) ∨ (((((p1 → (p2 → (p1 ∧ p4))) ∧ p2) ∨ p1) ∨ p4) ∨ ((p1 → p3) → p5))) ∧ (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977227531617866277148043863709 : (((True ∧ ((p2 ∧ (True ∧ ((((True → False) → (p2 ∨ p1)) ∧ p4) → (True → True)))) ∧ ((p1 → True) → (p2 ∧ ((True ∧ p2) → p4))))) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- One of the premise coincides with the conclusion.
  exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345547657071907036891815357014 : (p3 → (((((p4 ∨ p1) → False) ∧ (p2 ∧ p1)) ∨ ((p5 → ((((p1 ∧ p2) ∧ p3) → (p4 ∨ (p4 ∨ p2))) → False)) ∨ (False → False))) ∨ p5)) := by
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
theorem thm_5_vars_688175941304192455012180582279 : ((((((True ∧ p2) ∨ p2) → ((True ∨ (p2 ∨ (((False → p2) ∧ p1) → p1))) ∧ p5)) ∧ (((p1 → False) → False) ∧ ((p1 ∧ p2) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255742310220616204147664492949 : ((True ∨ True) → (((p1 ∨ p3) ∨ ((((p5 ∨ p4) ∧ False) ∧ (p5 ∨ ((p1 ∧ (p2 → (p4 ∧ p3))) ∨ p1))) → p5)) ∧ ((True ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147402354368898476891253492178 : ((((p5 ∧ (p2 ∧ (p4 ∨ (True ∨ p5)))) ∨ ((((p4 → p5) ∨ p5) ∧ (True → (True ∨ p5))) → False)) ∨ True) ∨ (p3 ∨ ((p3 ∧ p3) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182645647578554997082053885133 : (((((p5 ∨ (p3 ∧ p3)) ∧ p5) ∨ p1) → (True ∨ (True ∧ p4))) ∧ ((p2 ∨ p3) ∨ (False ∨ ((((p5 → p2) ∧ p4) ∨ p2) ∨ (p3 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
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
theorem thm_5_vars_49927866606036223489995167529 : ((((p3 ∧ (((((True ∧ (p5 → p5)) ∨ ((p3 → p4) → p3)) → False) → (False ∧ False)) ∨ p1)) → p4) ∧ ((p4 ∨ True) ∨ (p3 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111040530814425280214565005057 : ((((((p2 ∨ p1) ∧ ((p3 ∨ ((True ∧ p2) ∨ (False ∨ True))) ∨ (True ∧ True))) ∨ False) ∨ (((p1 → p3) ∨ p5) ∨ True)) ∧ True) ∨ (True → p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802096115246884890855179544116 : (((p2 → (True ∧ (True → ((p4 ∧ (p4 ∨ ((p5 ∧ (p1 ∨ ((True ∧ (p2 ∧ p4)) ∨ (p2 ∨ p5)))) ∧ (False ∨ (True ∨ p1))))) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164864366849691497776917897747 : (((p3 ∨ (((False → (p4 → False)) → (p4 ∧ (p1 → (p3 ∧ p1)))) → (p3 ∧ p3))) ∨ True) ∨ (True ∧ (((False ∧ p1) → False) ∨ (p5 → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64277874345916734829518877818 : ((False ∨ (p1 → ((((p2 ∨ (p3 → True)) → (((p5 ∨ (False ∨ p5)) ∨ ((False → p1) ∨ p4)) ∧ (p2 ∨ (True → True)))) ∧ True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157804960299141695156366417391 : ((((((p4 → (p4 ∧ (False → p4))) → (p3 ∨ p1)) → p3) ∧ p4) → (((p2 → p1) → p1) ∧ False)) ∨ ((False ∧ False) ∨ ((False ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_48976315984978662514630896800 : ((((((p3 ∨ (p5 → ((p1 → (p4 ∨ False)) → ((p5 → True) ∧ p1)))) ∧ p4) ∨ (False ∧ (p5 ∨ p3))) ∨ p1) ∨ ((True → p3) → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_164588670531022522843741964753 : ((((p2 ∧ p1) ∨ (p5 → (((p2 → ((p2 ∨ p1) ∨ p4)) → (p1 → p5)) → p4))) ∧ p5) ∨ ((p5 ∨ True) ∨ ((False → (p5 → p4)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66184863312221449262147047303 : ((p5 ∨ ((p1 → ((p2 → False) → (((((p1 → True) → True) → (p2 ∨ (p1 → p3))) ∧ False) ∧ p5))) ∨ (((p5 ∧ False) → True) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_48416961449112921096108518429 : (((p2 → (False ∧ ((p3 ∧ (True ∧ ((p5 → p3) → ((p2 ∨ (p1 ∨ (((p1 ∨ p1) ∨ p4) ∧ p2))) ∧ p1)))) ∧ True))) → (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51882941770690219449687883024 : (((((((True → True) ∨ p5) ∨ (p5 ∨ (p2 → (p2 ∧ (p3 ∨ p3))))) ∨ False) → p3) ∨ (p3 ∨ (False → ((p4 ∨ (True → True)) ∧ p4)))) ∨ p1) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153587485540631001680296412720 : ((False → ((p3 ∨ (((p1 ∧ True) → p4) ∧ (p5 ∧ True))) ∨ (p3 ∧ (((p1 ∨ p1) ∧ (p1 ∧ True)) → p1)))) → ((False ∧ p4) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314655300850124313868834218387 : (p3 ∨ (((((False ∨ p1) → p4) ∨ p4) ∨ ((((p5 ∨ p4) ∨ p1) → p3) ∨ (True ∧ p2))) ∨ ((p1 → (False ∧ (p5 ∨ True))) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_255183546372660872971268370573 : ((p4 ∧ p4) → ((p3 ∧ (((p4 ∧ (((p3 ∨ p2) ∧ p4) ∨ False)) ∨ (((p4 → False) → ((p2 ∨ p3) ∧ p4)) ∧ p4)) ∧ (p1 ∧ False))) ∨ p4)) := by
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
theorem thm_5_vars_726295008709417879079447268274 : (((((p2 ∨ p2) ∨ p3) ∨ ((p4 → p2) → ((p5 ∨ (p3 → ((p4 ∨ p4) ∨ (((p3 ∨ (p4 ∨ (p2 → p5))) ∧ p3) ∨ p4)))) ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353915897843579125780991429437 : (p4 → (p2 → ((((((True ∨ p2) ∨ p3) ∧ (p5 ∧ False)) ∧ (p1 ∨ ((False ∧ p2) ∨ p3))) ∨ True) ∧ (p4 ∧ ((True → (p3 → p5)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201291862043252299625792336123 : ((p4 → ((True ∨ (p1 → (p3 ∧ p5))) → p4)) → ((((p5 → p5) → (p4 ∧ p1)) ∧ p4) ∨ (p3 ∨ (((p3 ∧ True) ∧ (p5 ∧ False)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62770605976980720233573365907 : ((p4 ∧ (((((p4 ∧ (p1 ∨ (True ∧ (p2 ∧ p4)))) ∧ p1) ∨ (True → ((p2 ∨ (p4 → p2)) ∨ p3))) → p2) → ((p5 ∨ p1) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118612435565947061305861176729 : ((p4 ∨ ((((((True → p2) → p3) ∨ True) → p2) ∧ ((p4 ∨ False) ∧ (p4 → p3))) ∧ ((p5 ∧ ((False → p5) → p3)) ∧ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614329789337452570238129616707 : ((((((p4 ∨ p1) ∧ (p5 → ((p3 ∧ True) ∧ (p5 → (p3 → (p5 ∧ (p2 ∧ (False ∨ (p4 → p1))))))))) → ((p3 ∨ True) ∨ False)) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111406179347927313723087814268 : (((p2 ∨ (((p5 → p3) ∨ (((True ∧ ((p5 ∨ False) ∨ True)) ∨ p3) ∨ False)) ∧ (False ∨ ((p5 ∧ p3) ∧ (p4 → p2))))) ∧ p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136841768446399780568901083775 : (((p2 ∧ p3) ∨ ((((p4 → p3) → (((p3 ∨ p3) → ((p2 ∨ p3) → p1)) → p5)) ∧ (p3 → p2)) ∨ (p5 ∨ False))) ∨ (p1 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137636109483046294472548900977 : ((False ∨ (((((p4 ∨ True) ∧ ((((p5 → p1) → p3) ∧ True) ∨ (False ∨ p4))) → False) ∨ False) → ((p1 ∨ p1) ∧ p2))) ∨ (p4 ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_817553263156014662999310668625 : (((((p4 → ((p2 ∧ ((((p5 ∧ False) → ((p5 ∨ (p4 ∧ p5)) ∨ True)) → ((False ∨ (p2 ∧ p5)) ∧ False)) ∨ p1)) ∨ p1)) → False) ∧ p1) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → ((p2 ∧ ((((p5 ∧ False) → ((p5 ∨ (p4 ∧ p5)) ∨ True)) → ((False ∨ (p2 ∧ p5)) ∧ False)) ∨ p1)) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55911848144800682004725705811 : (((p5 ∨ (True ∨ (p1 → True))) ∧ (p3 ∧ ((p2 ∨ (p3 ∨ p4)) → ((p5 ∧ (p3 ∨ (p2 ∧ ((True ∧ (p3 ∨ p2)) ∧ True)))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60473708808231248534234288072 : (((p5 → p4) → (p4 ∨ ((((((p3 ∨ p1) → p1) ∧ p5) ∨ p1) → (((p1 → (True ∨ p4)) → False) ∨ ((True → p3) ∧ False))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192055858243323183582087458846 : ((p3 → ((((p2 ∨ p2) → p5) → (p5 → p2)) ∨ p3)) ∨ (((p1 ∧ (p5 ∧ p3)) → p1) ∧ (((((p4 → p3) ∨ p2) → p5) ∧ True) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357100921200675150379269952492 : (p5 → ((p4 ∧ (True ∧ p5)) → ((p4 → p2) → ((p5 ∨ ((p4 ∨ (p4 ∨ p4)) ∧ p5)) → (p5 ∧ ((False ∧ (p4 ∧ p5)) ∨ (p1 ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h2.left
      let h15 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h2.left
        let h21 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h2.left
        let h26 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h2.left
    let h31 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h2.left
      let h39 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h2.left
        let h45 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h2.left
        let h50 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57345058923861418858791107299 : (((p2 ∧ (p3 ∨ p3)) ∨ (p2 → ((p4 ∧ ((((False → (p5 → False)) ∧ p4) → p1) ∧ p1)) ∨ (True → (True ∨ (p2 → (False ∧ p5))))))) ∨ p1) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249097276030270297372256845747 : ((p4 ∨ p1) ∨ (p1 → (p4 ∨ (((p5 ∧ (p2 → True)) ∨ ((((p2 ∧ True) ∨ (False → p2)) ∨ (((p4 ∨ False) ∧ False) ∨ False)) ∧ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472753985487517834327094938658 : (((((((p1 ∨ (p3 ∧ ((p2 ∨ p2) ∧ p5))) ∧ p4) ∨ False) ∧ p1) → (False ∨ (p2 ∨ ((((p1 ∧ p4) ∨ p5) ∧ (p3 ∨ p4)) ∨ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663557087829700018763993597924 : ((((True ∧ ((((True → p2) ∧ p1) ∧ True) ∧ ((p2 → ((((False → (p2 ∨ p2)) → p5) ∧ p1) ∨ p1)) ∨ (p2 → p1)))) → (True → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316996829640030939891560198573 : (p3 ∨ (p3 → ((((p5 ∨ p1) → (True ∧ (p5 ∧ (p5 ∨ p5)))) ∧ p4) ∨ ((p3 ∨ p1) ∨ (True ∧ (True ∨ ((p4 ∨ (True ∨ p3)) → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752640002114382738363195654403 : (((False ∧ (((((p2 → ((p3 → p3) ∧ p5)) → False) ∨ ((p5 → ((p4 ∧ (False ∨ (p2 ∧ p1))) ∨ (p5 → p5))) ∧ True)) → p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139920893879818686079841857846 : (((((False → ((True → p1) → (p4 ∧ True))) → (p1 → False)) → (False → (p3 → (True → (p1 ∧ True))))) ∧ (p3 ∨ p2)) → ((p2 → p3) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117867508406275257520910303595 : ((p5 ∧ ((((((p3 → (p4 ∧ (p5 ∧ (p4 ∧ True)))) ∧ (True ∨ p2)) ∧ False) ∨ p2) ∨ (p4 → (p1 ∨ (p3 → p4)))) ∨ p3)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336132775972182948104659443630 : (p1 → ((((p4 ∨ p2) → (True ∧ (((((((False ∨ p2) ∨ (False → True)) ∧ p2) ∧ False) ∧ p1) ∨ (p4 ∨ p4)) ∧ (p2 ∧ p4)))) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251113143193286900901974596592 : ((p2 → False) ∨ ((((True → (p4 → False)) ∧ (True → (p1 ∧ (p4 ∨ p2)))) → (True → ((False ∨ ((p4 ∨ p5) ∧ True)) → (p2 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48762692267556590714665456026 : ((((p3 ∧ p1) ∨ (((p4 ∧ ((((p5 ∧ (True ∧ p3)) ∧ False) ∨ (True → True)) ∨ (p1 ∧ p3))) ∨ True) ∨ False)) ∧ (p2 → (p2 ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111018758551423865584481090302 : (((((p2 → (((True ∧ (p4 ∧ False)) ∧ (p3 → (p3 ∧ ((p4 ∧ p2) ∨ p2)))) ∨ p5)) ∧ p1) → ((p4 ∨ p4) ∧ p3)) ∧ p3) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149360202792448833976010003957 : (((p5 ∨ p5) → (p3 ∨ ((((False → (False ∨ (((True ∨ p4) ∨ True) → (p5 ∨ False)))) ∨ p3) ∨ p5) ∧ False))) ∨ (((p3 → p3) ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41033918021371012129568525945 : (((((p2 ∧ ((p1 → ((p1 → p2) ∨ p2)) ∨ ((p2 → False) → ((p1 ∧ True) → False)))) → ((p1 ∧ True) ∧ True)) → (p4 ∨ p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733276667218536353687684566615 : ((((p3 ∧ p4) ∧ ((p5 ∧ ((p4 ∧ ((p4 ∧ (True ∨ ((p2 ∨ True) → p5))) → ((p3 ∨ p3) ∨ p1))) ∧ (True → p3))) ∨ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211337785802991646084008155230 : (((p3 ∨ True) ∨ (p5 ∧ p3)) ∧ ((((p3 ∧ (p4 ∨ p2)) ∨ ((p4 ∧ p3) → ((p4 ∨ False) ∨ p4))) ∧ ((p1 → (False ∨ p5)) ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670110098663771452967324096465 : (((((p1 → (p5 ∨ (p5 ∧ (p5 ∧ p4)))) ∧ (p4 ∧ (True → (p5 ∧ (True ∨ (((p5 ∨ p4) ∨ False) ∧ p1)))))) ∨ (p1 → (False → True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657738917003752599726779512003 : ((((True ∧ (((((p2 ∨ (p2 ∧ True)) → p5) ∧ (p2 ∨ p2)) ∨ (((p3 ∧ p2) → (p1 ∨ (p2 ∧ p2))) → p1)) ∨ True)) ∨ (p5 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_149524989737892387706714021391 : ((p1 ∧ (p2 ∨ ((p2 ∧ (p2 ∧ p2)) ∨ (((True ∨ (((p4 ∧ p2) ∨ True) ∨ p2)) → True) ∨ (False → p4))))) ∨ (False → ((True ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802944060706742957077638195997 : (((p3 → ((((((p3 ∨ ((p5 → False) ∨ True)) → ((p2 ∨ ((True → True) ∧ p1)) ∨ (p1 ∨ p3))) ∨ (p3 ∧ False)) → p1) → p1) ∧ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ ((p5 → False) ∨ True)) → ((p2 ∨ ((True → True) ∧ p1)) ∨ (p1 ∨ p3))) ∨ (p3 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h9
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173433969133243004985881985924 : ((p5 → (p4 → ((p5 → False) ∧ (((False → (p3 → (True ∨ p4))) → True) ∧ p5)))) ∨ ((p5 → p1) → ((True → p5) → ((p3 ∨ p5) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137847319684593043077409387687 : ((p3 ∨ (((p3 ∧ False) ∧ True) ∧ ((p3 ∧ ((((p3 ∧ p3) ∨ (p1 ∨ p3)) → (p5 ∨ False)) ∨ p2)) ∨ (p2 → False)))) ∨ (p3 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133038627972162181685833299274 : ((p5 ∨ (p3 ∨ ((True → (p2 ∨ (p5 → ((p5 → p1) ∨ p3)))) → (p1 ∨ (True ∨ ((p1 → (p2 → p1)) ∨ False)))))) ∧ ((p1 ∨ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746275976074407256157875509412 : ((((p1 ∨ p5) → (((p3 ∧ p5) ∨ (p2 → False)) ∨ ((p2 ∨ ((p4 ∧ (False → ((False ∧ ((True ∨ p4) ∧ p1)) ∨ True))) ∧ p4)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322594043809007779393776808001 : (p5 ∨ ((p1 → (((p4 → ((((p1 → p3) → (((p4 → p5) ∧ (p2 ∨ False)) ∨ (False ∧ False))) ∧ p5) ∧ p3)) ∨ (False ∨ True)) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68497569111911946378819132405 : ((p3 → (p2 ∨ ((p1 ∨ ((False ∨ p5) ∧ (False ∧ ((False ∨ (p4 ∧ ((p4 ∧ False) ∧ False))) ∨ p2)))) ∨ (((p3 ∨ False) ∨ True) ∨ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_613739086333375531956696656226 : ((((((p4 → p4) → (((p4 ∨ (p1 → p5)) ∨ p4) → (p2 → (((p2 ∧ p5) → p2) ∧ (p2 → False))))) ∧ (p1 ∨ (False → p4))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117900138635327752382329983962 : ((p5 ∧ (((((p2 → (p5 ∧ (p4 ∨ p1))) → False) ∧ p2) ∧ (p2 ∨ ((p3 ∧ p5) ∨ p2))) ∧ (p3 → ((p5 ∨ p5) → False)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63054909383188049355117714485 : ((p5 ∧ ((((True ∨ p4) → p4) ∨ ((p2 ∨ (p3 ∧ ((True ∧ (True ∧ p1)) ∨ p3))) ∧ (((True → (True → p2)) → p3) ∧ p5))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314224597136521450456704010870 : (p3 ∨ (((((p2 ∨ p5) ∧ True) ∨ ((p5 ∨ p2) → ((False ∧ (p2 ∨ p4)) ∨ (p1 → ((p2 → False) → p4))))) ∧ p2) ∨ (p1 → (p1 ∨ p2)))) := by
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
theorem thm_5_vars_46078716704754931678880162113 : ((((((p3 → ((p1 ∨ True) → ((((p5 ∧ p5) → (p4 ∧ False)) ∧ True) → p1))) → p1) ∧ (p5 → (p3 → False))) ∨ p3) ∧ (True ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168851965897116315857428556556 : ((p3 ∨ (True ∨ (p4 → (((((p5 ∧ p3) ∨ (p2 ∧ True)) ∨ (p2 ∨ p5)) → False) ∧ p1)))) → (p1 → ((p4 ∨ p1) ∧ (p5 → (p1 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306460197052194681187213723610 : (p1 ∨ ((p4 ∨ p1) ∨ (((p1 → p1) ∨ p1) → ((True → False) → (((p1 ∨ (p5 ∨ (((p2 → p2) ∨ (True → False)) ∧ p2))) → p3) → p2))))) := by
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
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38184154447686170470383171062 : ((((p1 ∨ (((False → p4) ∧ ((((p4 → p5) ∨ (p3 ∧ (True ∨ True))) ∧ True) ∧ (False ∧ p5))) ∨ p4)) ∨ (True → (p2 → p4))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202508852135158352855130674174 : ((((p4 → p5) ∨ p3) ∨ (False → False)) ∧ (((((p2 → (p4 ∧ (p5 → True))) → p3) ∨ p2) ∧ (((p1 ∨ (p2 ∨ True)) ∧ p1) → p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184853703380462057423293091168 : ((((p5 ∧ p2) ∧ p1) ∧ (p1 ∧ (p5 ∨ ((p4 → p5) ∨ p4)))) ∨ ((True → (p3 → (p2 → (p5 ∨ p3)))) ∧ ((True → (False → p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356654835634336864259377661590 : (p5 → (((p5 ∨ (p1 ∨ (p1 → p3))) ∧ (p3 → p3)) → ((p3 ∧ (((p5 ∧ p5) ∨ (False → False)) ∧ True)) ∨ ((p3 ∨ (p5 → False)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45086222867232088890359621449 : ((((p3 ∧ p2) → (p4 → ((p5 ∧ False) → ((p3 → p1) → ((p1 ∧ (p2 ∧ ((p3 → p1) ∨ (p2 → (p5 → p3))))) ∨ p2))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602816205406609038512860936583 : ((((p1 ∨ ((((True ∧ (((p1 ∨ p3) ∨ p1) → (p5 ∨ (p3 ∧ ((p2 → (p2 → True)) ∨ p5))))) ∨ True) ∧ (True → p5)) ∧ p1)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56302472490063631976389164379 : (((((p2 ∨ True) → False) ∧ p5) → (False ∨ ((p2 ∨ (((p3 ∨ (p4 → ((p2 ∨ (True ∧ (p3 ∨ True))) → False))) ∧ p4) ∨ p5)) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619721589549262213005688784599 : (((((True ∨ True) ∧ ((p4 ∨ p3) ∧ ((p3 ∧ (p2 → (((((p4 ∨ (True → (p5 ∨ p4))) ∧ p5) → False) ∧ p4) → p1))) ∨ True))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_305719827075538533110492078968 : (p1 ∨ ((p2 ∨ (True ∨ (True ∧ (p1 ∧ ((p5 ∨ p2) ∨ p4))))) → (((p2 ∨ (p4 → p1)) ∧ (p2 → (p4 ∨ True))) ∨ (p2 → (p2 ∨ p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66081123005815518538830089997 : ((p5 ∨ ((p5 ∨ ((((((p1 ∨ (True → p2)) ∧ ((p1 ∧ (p1 ∨ p1)) ∨ p1)) ∧ p5) ∧ True) ∨ p3) → ((p5 → False) ∧ p2))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198578977546457134701502877335 : ((p1 ∨ (p5 ∧ (((True ∨ False) ∧ p5) ∧ True))) ∨ ((((p4 ∨ (p5 ∧ False)) ∨ (((p3 ∨ p4) ∧ p5) → p4)) ∨ (p4 → p4)) ∨ (p2 ∨ p4))) := by
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
theorem thm_5_vars_149120781969604328219408085229 : (((p1 ∧ False) ∧ (((p1 → ((p5 ∨ (p3 → p5)) → ((p1 → p3) ∧ (p4 ∧ (p2 → p5))))) ∨ p3) → p5)) ∨ ((p1 → (p4 ∨ True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324028246820167055047643082251 : (p5 ∨ (((p3 ∧ p4) ∨ ((p1 ∨ (p5 → (p5 ∨ ((p3 → p3) ∨ False)))) ∨ p3)) → ((p5 → False) ∨ (((p4 → (False ∧ p2)) ∧ True) → True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146900681257768400791120877018 : ((p5 → (p5 → (True ∧ ((p5 → (p3 ∨ (p2 ∧ p3))) → (p2 ∨ ((p4 → p1) ∨ (p2 ∨ (p3 ∧ True)))))))) ∧ ((p2 ∨ (True ∨ p2)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725479645872268779599293837 : ((((((p1 → p4) → False) ∨ False) ∨ p1) → ((p5 ∧ ((True ∧ (p3 ∧ False)) ∨ ((p2 → p4) ∨ (p1 → True)))) ∧ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301165893080791770588260469715 : (False ∨ ((p5 → (((p2 → (p1 ∨ p4)) ∧ p4) ∨ p1)) ∨ (((False → False) → (False → ((True → p5) → (p3 → (p5 → p3))))) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_337756362324613088424307892688 : (p1 → (((((((p4 ∨ p5) ∨ (True → p2)) → (p2 ∨ (p3 ∧ p5))) → p2) ∧ p5) ∨ False) ∨ (True ∧ (p4 ∨ ((True ∨ True) ∨ (True ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126544246480242816746528648133 : ((p3 ∧ ((((True → ((True ∨ ((p3 → (p4 ∧ (p1 ∨ False))) → p3)) ∨ (((p4 ∧ p1) → True) → p2))) → p5) ∨ p3) ∧ p4)) → (p2 → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111946497486682800376576669822 : (((((((p1 → p3) → p2) ∨ (p5 ∧ p4)) ∨ p3) ∧ ((p3 → p2) ∨ ((p1 ∨ (True ∨ (p3 ∨ (True ∨ p1)))) ∧ p1))) ∨ p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185499191038092288883118576359 : ((p2 ∨ ((((p4 ∧ p3) ∨ p5) ∨ p4) ∨ (False → (p5 → True)))) ∨ (((False ∧ p4) → p5) → (((p5 ∨ p4) → (p5 → p4)) ∧ (p2 ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41061021070352808316468180101 : ((((p1 ∧ (p5 → ((p2 ∨ ((True ∧ ((p1 ∧ (((p5 ∨ True) ∨ p2) ∧ p3)) ∧ (p5 → False))) → p4)) ∧ p5))) → (p4 ∨ p1)) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_207465452409747998170157649074 : (((True → (p5 → (p5 → p1))) ∨ p5) → (p1 → ((p1 ∧ p4) → ((False ∨ ((True ∨ p5) → (p2 ∨ p4))) ∧ ((False → (False ∧ p4)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h17
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h19
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26630386714742978696112611846 : (((p3 ∧ False) ∨ ((p5 ∨ ((p3 ∧ ((p2 → (True ∧ ((p4 → (p3 ∨ ((p4 ∧ p4) → True))) ∨ p5))) → p5)) ∧ True)) ∨ (p2 ∨ True))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601968254353506493601258864292 : ((((p4 ∧ (p2 → (((p5 → ((((p2 → (p1 ∧ ((p3 ∧ (p4 ∨ p1)) → p5))) ∧ p4) ∧ (p2 → p4)) ∧ False)) ∧ p5) → p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



