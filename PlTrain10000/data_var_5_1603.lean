variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174361620552856700760803602323 : (((p5 ∧ (p5 ∧ ((p4 → (p1 ∨ (True ∧ p3))) ∧ p1))) → (p4 ∧ (p2 ∨ p5))) → (((p2 → (True ∨ p4)) → (p5 ∨ p3)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191933932917909892694134857861 : ((True → ((p5 ∨ (p4 ∨ (p3 ∨ p4))) ∨ (p1 ∨ p3))) ∨ ((((False ∨ p3) → p4) → (p2 → ((True ∧ ((p2 ∨ False) ∧ p3)) → p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389888667700111675357622637487 : (((((((False ∨ (p1 ∧ ((p5 ∨ p4) ∨ (p5 ∧ p1)))) → p1) → True) → ((True → (((p3 → p4) ∨ (True → p3)) ∧ False)) → p5)) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262101599479280844397747041721 : (True ∧ ((((((((True ∧ False) ∧ (p1 ∨ False)) → p3) → (((p1 → p5) ∨ ((p1 → True) ∧ p3)) → p2)) ∨ (True ∨ p3)) ∨ p5) ∧ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_171804782039224098180300352648 : (((((False ∨ (p2 ∧ (p2 ∨ True))) → (p5 ∧ False)) → ((p2 ∨ p2) ∨ p1)) → False) ∨ (False → ((p3 ∧ ((p4 ∨ p5) → (False ∨ p1))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324212398836812202028984183512 : (p5 ∨ ((p3 ∨ ((False ∧ p4) → (((p1 ∧ False) ∨ p5) ∧ p1))) → (((True ∨ True) → False) → ((False ∧ p5) ∧ (False → ((True ∨ False) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44709348333341104321268298785 : (((((p3 → p4) → (p1 ∨ p3)) ∧ ((((p2 ∧ (False ∨ (p3 ∨ True))) ∧ ((False ∧ True) → p5)) → p2) ∧ ((p4 ∧ p1) ∨ p2))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86752821489783819251884480043 : (((((((False → p1) ∧ p4) ∨ False) ∧ p5) ∧ p1) ∨ ((p1 → (p4 → ((((p5 ∧ (p2 ∨ (p3 ∧ p1))) ∧ p1) → p2) ∨ p1))) → p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p1 → (p4 → ((((p5 ∧ (p2 ∨ (p3 ∧ p1))) ∧ p1) → p2) ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113244465093299927161708795970 : (((((p5 → (p4 ∧ (False → p4))) ∧ (p5 → (p4 → (False ∨ (p3 ∧ (p2 → (p2 ∧ True))))))) ∧ (p1 ∧ p1)) ∧ (True ∧ p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354966530748192987105586734307 : (p5 → ((p3 → (((p1 ∧ ((p1 ∨ (p1 ∧ ((p5 → (True ∨ (False ∧ p3))) → (p4 ∨ ((True ∨ p2) ∧ p3))))) ∨ p1)) ∨ True) ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47067038517950043689342357916 : (((((False ∨ False) ∧ (((False → (False ∨ p1)) ∨ ((((False ∨ p5) → p3) ∨ p1) ∨ (True → p2))) ∨ p2)) ∨ (p5 ∧ False)) ∨ (p4 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172438695484530763834303334763 : (((((p2 → False) ∨ p5) ∧ p4) ∨ ((((p2 ∧ p4) ∨ (p3 → True)) ∨ p2) ∨ p4)) ∨ ((p4 ∧ True) → ((p5 → ((True ∧ True) ∨ False)) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665881709848285111595963667433 : ((((((((p3 ∧ p5) ∨ p5) → (p5 ∨ (p3 ∧ (True → (p4 ∧ False))))) → ((p3 → (p4 ∨ p2)) → True)) → p3) ∧ ((True ∧ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111040873561826043503978675596 : (((((((((p5 ∧ ((True ∧ (False ∨ p5)) ∧ True)) → True) ∧ p5) ∨ p4) ∧ p2) → p4) ∨ ((p5 → p5) ∧ (p2 → p4))) ∧ p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82339651245299723097582583660 : ((((((p3 ∧ p5) ∨ (p2 → (p3 ∧ (p5 ∨ (p5 ∨ True))))) ∧ p2) ∧ (True ∧ ((p1 ∨ p1) → p3))) ∧ ((p4 → True) ∧ (p3 ∨ p5))) → p3) := by
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h5.left
    let h12 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h24 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h25 := h17 h24
      -- We need to get the left conjuct of h25 based on <expert-advice>.
      let h26 := h25.left
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37377468039371643092224869512 : ((((((p4 ∨ (p4 → ((((p3 ∨ (p1 → p3)) ∧ (p2 ∧ p3)) ∨ (p1 ∧ (p1 ∧ p2))) ∧ (p5 ∧ p4)))) ∨ False) → p2) ∨ p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141194981284146397553427470366 : ((((p2 ∧ p2) ∧ (p1 ∧ (True ∧ p1))) ∨ ((True ∨ p5) ∧ ((p5 → False) → (True → (((True → p1) → True) ∨ p2))))) → ((p3 ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330590728822090614786450779048 : (True → (p5 ∨ (p4 → (((((((p2 → p5) ∧ True) → (False → True)) ∨ ((False ∧ p1) ∧ p2)) → p2) ∧ (((True ∨ False) ∨ p2) ∧ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187460920663784759130465864234 : ((True ∨ ((p5 ∧ False) ∧ (p1 ∨ (p5 → ((p1 → p3) ∧ p5))))) → (((p4 ∨ (p3 → (p4 ∧ (p4 ∨ p2)))) ∨ (p5 → p5)) ∨ (p3 ∧ p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787150516110366867393165700924 : (((p4 ∨ ((p4 ∨ p2) → (False ∧ (p3 → (((((p2 → True) ∨ (p1 ∧ (False ∧ p2))) → (p2 ∧ False)) ∧ p1) → ((False ∨ False) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687584757954407093003814410855 : ((((((False ∨ (((p4 ∧ p5) ∨ (p4 → (False → p2))) ∧ p2)) ∨ (p2 → p1)) → False) ∧ (((p5 → p3) ∨ ((p2 ∧ p5) → p1)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221242652292302816659618974413 : (((p2 ∨ p1) ∨ True) ∧ (((True → p5) ∧ ((True → (p4 ∨ ((p2 ∧ p2) ∨ (((p1 ∧ False) → (True ∧ p2)) ∧ True)))) → (p3 ∨ p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802065189457480872575341930457 : (((p2 → (True ∧ (((True → ((((True ∨ p4) → ((p1 ∨ (True ∧ False)) ∨ p2)) → ((p2 ∨ False) → p1)) ∨ p1)) ∧ (p1 ∧ False)) ∨ p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300779539416950904921670931201 : (False ∨ ((((p4 ∧ (((p2 ∨ p5) → (False ∨ p3)) ∨ p1)) ∧ (p5 ∧ p1)) ∨ (p1 → True)) ∨ ((((True ∧ p2) → p4) → p4) ∨ (p3 → False)))) := by
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
theorem thm_5_vars_46952698569261365190519354678 : ((((p4 → ((p5 ∧ False) ∨ (((((p2 ∧ (False ∧ (p2 ∧ p1))) ∨ False) ∨ p2) ∨ False) ∧ ((False ∧ p2) ∧ False)))) ∨ True) ∨ (p3 → False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662679021160822717152537342403 : (((((((p2 ∨ p4) ∨ True) ∨ True) ∨ (((((p3 → False) ∧ p4) ∨ (((False ∧ p5) ∨ p2) ∨ p1)) ∧ p3) ∧ (p5 ∧ p4))) → (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54648285502222170877311964636 : ((((((p3 → p4) → (p5 → False)) ∨ p2) ∨ False) → ((p2 → ((p1 ∧ (((p4 ∨ p2) ∧ p3) → False)) ∧ p3)) ∨ (True → (False → False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614995853377461638211577097741 : ((((((((p4 ∨ p5) → p3) ∧ False) → (True ∧ (((p4 ∧ p5) ∧ (True ∨ p2)) → (p2 ∧ p5)))) → (False ∨ ((p3 → p1) ∧ p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49117141046743648112735150348 : (((((((p5 ∨ True) ∧ True) ∨ ((p3 ∧ True) ∧ ((True ∨ p5) ∧ True))) ∨ False) → ((True ∨ p4) → (False ∨ True))) ∨ ((p4 → p4) ∨ False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172684634108536672490552479074 : (((p1 ∧ True) ∨ ((True ∨ (((p4 ∧ (False ∨ p2)) ∨ True) ∨ p2)) → (False ∨ p1))) ∨ (True → ((True → p2) ∨ (((False ∧ p2) ∧ p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158217330176424145347244417936 : (((p1 ∧ (False ∧ True)) ∧ ((p4 → ((p1 ∨ p1) ∧ p1)) ∨ (p3 ∨ (p2 → ((p4 ∧ p2) ∨ p5))))) ∨ ((False ∨ (p2 → (p3 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58942486953503294878909804969 : (((p1 ∧ p5) ∨ (((p1 ∨ (p3 → False)) ∧ p1) ∨ ((p4 ∨ ((((p1 → (False → (p4 ∨ p2))) → p5) ∧ False) ∧ p5)) ∨ (False → p4)))) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156616806400431052728276534354 : (((((((p3 ∨ ((p2 ∧ p4) ∧ (p2 ∧ (p3 ∧ p1)))) ∨ (p5 → p2)) ∧ p2) ∧ p1) ∨ True) ∧ p3) ∨ (True ∨ (p1 → ((p1 ∧ False) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485504082204204038695545296702 : ((((((True ∧ p3) ∨ (p2 ∨ p3)) ∨ False) ∨ (p3 → (p2 ∨ ((p3 ∨ (True ∧ (((p2 → (p4 → p3)) → (p2 ∨ p3)) ∧ p1))) ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340753891584494735847010975847 : (p2 → ((((False → p2) ∧ (((p4 ∨ ((p5 ∨ p2) → (((True ∨ p1) ∧ (p2 ∨ p2)) ∧ p3))) ∧ ((p4 → False) ∨ False)) → p4)) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111437071628256894180795690017 : (((p5 ∨ (((p4 ∧ p2) → (((p1 ∧ False) ∨ ((p1 → p2) ∨ (p3 ∨ (p4 ∨ p3)))) → ((p5 ∧ p4) ∨ p2))) → p4)) ∧ True) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190109833472325807999450644857 : (((((p2 ∧ p1) ∨ p2) ∧ ((p3 → p1) ∨ p1)) ∧ p4) ∨ (((True ∨ ((p1 ∨ False) ∨ True)) ∨ True) ∧ (((p4 → p4) ∨ (False ∧ p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342976555533874292600024425788 : (p2 → (((True → (False ∨ p3)) ∨ p1) ∨ (p5 → ((p3 ∧ ((p1 → (p1 → p4)) ∧ (p4 → (((p4 ∧ False) ∨ (True ∨ p2)) → p3)))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122471724162446972814201452454 : (((((False ∨ p1) ∨ p2) ∧ (((p5 ∨ (p5 ∨ (p4 ∧ (p2 → ((p4 ∧ p5) ∧ True))))) ∨ True) ∧ (True → False))) ∨ (False ∧ p2)) → (p1 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h4.left
        let h9 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- One of the premise coincides with the conclusion.
              exact h7
            case inr h14 =>
              -- Conjunctions on the left can always be decomposed.
              let h15 := h14.left
              let h16 := h14.right
              -- One of the premise coincides with the conclusion.
              exact h7
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h4.left
      let h20 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h24 := h20 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
            have h27 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h20, we can now drive its conclusion.
            let h28 := h20 h27
            -- False on the left can always be used.
            apply False.elim h28
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h20, we can now drive its conclusion.
            let h33 := h20 h32
            -- False on the left can always be used.
            apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h36 := h20 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- False on the left can always be used.
    apply False.elim h38
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h40.left
    let h42 := h40.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h42.left
        let h47 := h42.right
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h48
          case inl h49 =>
            -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
            have h50 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h47, we can now drive its conclusion.
            let h51 := h47 h50
            -- False on the left can always be used.
            apply False.elim h51
          case inr h52 =>
            -- Disjunctions on the left can always be decomposed.
            cases h52
            case inl h53 =>
              -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
              have h54 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h47, we can now drive its conclusion.
              let h55 := h47 h54
              -- False on the left can always be used.
              apply False.elim h55
            case inr h56 =>
              -- Conjunctions on the left can always be decomposed.
              let h57 := h56.left
              let h58 := h56.right
              -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
              have h59 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h47, we can now drive its conclusion.
              let h60 := h47 h59
              -- False on the left can always be used.
              apply False.elim h60
        case inr h61 =>
          -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
          have h62 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h47, we can now drive its conclusion.
          let h63 := h47 h62
          -- False on the left can always be used.
          apply False.elim h63
    case inr h64 =>
      -- Conjunctions on the left can always be decomposed.
      let h65 := h42.left
      let h66 := h42.right
      -- Disjunctions on the left can always be decomposed.
      cases h65
      case inl h67 =>
        -- Disjunctions on the left can always be decomposed.
        cases h67
        case inl h68 =>
          -- One of the premise coincides with the conclusion.
          exact h64
        case inr h69 =>
          -- Disjunctions on the left can always be decomposed.
          cases h69
          case inl h70 =>
            -- One of the premise coincides with the conclusion.
            exact h64
          case inr h71 =>
            -- Conjunctions on the left can always be decomposed.
            let h72 := h71.left
            let h73 := h71.right
            -- One of the premise coincides with the conclusion.
            exact h64
      case inr h74 =>
        -- One of the premise coincides with the conclusion.
        exact h64
  case inr h75 =>
    -- Conjunctions on the left can always be decomposed.
    let h76 := h75.left
    let h77 := h75.right
    -- False on the left can always be used.
    apply False.elim h76



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40255540692071147347202082828 : ((((p1 ∨ ((p1 → p2) ∧ (p2 ∨ (p1 ∨ (p1 ∧ (p1 → ((p3 → (False ∨ ((p3 ∨ p2) ∧ (p4 ∨ p2)))) ∧ True))))))) ∧ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168989985802998823390877052714 : ((p1 → ((True ∧ (p4 ∧ (((True → p3) ∨ (p2 ∧ True)) ∧ (True → (True → True))))) ∧ p3)) → ((p4 → (True → p1)) ∨ ((p1 → p1) ∨ p1))) := by
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
theorem thm_5_vars_63933694189748904516621707220 : ((False ∨ (((((((p1 → p2) ∨ p2) ∨ (p1 → (p2 → ((p1 ∨ p4) ∧ True)))) ∧ p2) ∧ (p2 ∧ (p5 ∨ p1))) → (p1 ∧ p5)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328119615358286342080999743743 : (True → (((((((p5 ∧ False) ∨ p2) → p2) → (p5 ∧ p4)) ∨ (p1 ∨ p1)) ∧ ((False ∨ (True ∧ p3)) ∧ (True ∨ False))) ∨ (True ∨ (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611786574135031810098161117379 : (((((p1 → ((p3 ∨ ((p4 → (p1 ∧ p5)) ∧ p4)) ∧ ((p4 ∧ p2) → ((p3 ∨ (p3 ∧ ((True ∨ p5) ∧ p4))) → p2)))) → p5) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_264412481458615123563011560402 : (True ∧ ((p4 ∨ (p1 ∧ (p3 ∨ p3))) ∨ ((((((p3 ∧ p4) ∨ (p4 → ((p3 ∧ p5) → p5))) → p2) → p1) → p3) ∨ (True ∨ (p1 ∧ False))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46916071522721889008231994899 : (((((p1 ∨ (p2 ∨ (p4 → ((p5 ∨ p2) ∧ p2)))) ∧ (((p3 ∨ p1) ∨ (p1 → True)) ∨ ((p2 → p5) → p4))) ∨ p4) ∨ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134520335185259347246341747404 : ((((p1 → ((((p5 ∨ p2) ∨ p1) ∨ p5) → (True → ((True → True) ∨ (((False → False) ∧ p5) ∨ p1))))) ∨ p4) → p5) ∨ ((True ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160687915593851993000871619916 : ((((True → p2) ∨ ((p1 ∧ p2) ∧ (p4 → p1))) ∧ ((p4 → (False ∧ (False ∨ False))) ∨ (p2 → True))) → ((p4 ∧ (True ∨ (p3 → p3))) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h14 := h8 h13
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
      cases h7
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h28 := h25 h27
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h30 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h31 := h25 h30
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h37 =>
        -- One of the premise coincides with the conclusion.
        exact h36
      case inr h38 =>
        -- One of the premise coincides with the conclusion.
        exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196777365772887014037247916704 : ((((p1 ∧ p4) ∧ ((True ∧ p1) ∨ False)) ∧ p5) ∨ (True ∧ ((False ∨ (((p2 ∨ True) ∨ (((p5 ∧ (p4 ∧ p1)) ∧ p2) ∧ True)) ∨ False)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53265890591412896231252410934 : ((((p5 → p4) → ((p4 ∨ (p4 ∨ ((p1 → p2) → p4))) → False)) ∨ ((False → (p3 ∧ (((p1 ∨ (True ∨ p3)) ∨ p5) ∨ p1))) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346633443254939622909862356146 : (p3 → ((p3 ∧ (((((False ∨ ((p1 ∨ False) ∨ (p2 → p5))) → ((p2 → p4) ∨ p4)) → p2) ∨ p5) ∧ (p3 ∨ p1))) ∨ ((p4 ∨ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55246494548705248715233769629 : ((((True → p2) ∧ ((p4 ∧ True) ∨ p2)) ∨ (p1 ∨ ((p3 ∨ ((p1 → (p5 → (((p1 → (True ∧ True)) ∨ p1) ∨ p1))) → p1)) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_52779595086267032839234243291 : (((((((p4 ∧ p3) ∨ (p2 ∧ (False ∨ True))) ∧ p3) ∨ p5) ∨ (True ∨ p4)) → ((p3 ∧ (True ∨ ((p1 ∧ p1) → (p2 → p1)))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190746239547661579745863737320 : (((True ∨ (p4 → ((True → p4) → False))) ∧ (p5 ∨ p3)) ∨ (((((p1 → (p2 ∨ (p4 → ((True → p4) → True)))) ∧ p4) ∨ p2) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172798675222670172075237844101 : (((p4 → True) → (((True → p2) ∧ (False → (p2 → p4))) → (p2 ∧ (p1 → False)))) ∨ (p3 → (p3 ∨ (True → (p2 ∨ ((True → p4) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596444914899551936558033043084 : (((((p2 → (p4 ∧ ((p2 ∨ p5) → (False ∧ False)))) ∨ (p1 ∨ (((((p1 ∧ False) → False) → p3) ∧ (p2 ∧ p4)) ∧ (p1 ∨ p4)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190358279241099098617751301696 : ((((p1 ∧ p1) ∧ (((p2 ∨ p5) ∧ p5) ∨ p3)) ∨ p3) ∨ ((False ∨ True) ∨ ((False ∨ p1) → (False → (p1 → (p4 ∨ (p4 → (p4 ∧ True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51950339475769618555062147211 : (((((p1 ∨ (True ∨ (p4 → p1))) ∧ True) → (p3 ∨ (((p1 ∧ p4) ∨ p2) ∧ p3))) ∨ ((False ∧ p4) ∨ (((False ∨ p3) → p1) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731212840459466575400255958074 : ((((p3 ∨ (p4 ∧ p1)) → (((False ∧ (p5 ∨ (True ∨ p1))) ∨ ((((p3 ∨ ((p1 ∧ p2) ∨ p3)) ∧ p3) → (p2 → p1)) → False)) ∨ True)) ∨ p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216858942757720382224499064843 : (((True ∨ (p5 → p5)) ∧ p3) → ((p2 ∨ (((p2 ∧ p1) ∧ ((True → p1) ∨ False)) → p1)) → ((True → (((p5 ∨ True) ∧ False) ∧ p1)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665781525745162125931605215984 : (((((((True ∧ (p5 ∧ ((p5 ∧ (p2 → (p2 → (p5 ∨ (p3 ∨ (p2 ∨ p4)))))) ∨ p5))) → p2) ∨ False) → p2) ∧ ((True ∧ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166086668395194442424982731377 : (((p4 ∨ p2) → ((p1 → p3) ∧ ((True ∧ ((p1 ∨ False) → (p5 ∨ (p2 ∨ p3)))) → p3))) ∨ ((((p1 ∨ p4) → False) ∧ (p4 ∨ p1)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114757291764525016162691304652 : (((p1 ∨ ((((((False ∨ True) ∧ p4) ∨ p3) → False) ∨ ((True ∨ p2) ∧ p4)) ∧ p4)) → (p4 ∨ (True ∧ ((False ∧ p4) ∨ p4)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_503439899653282600521329807102 : (((((p5 ∧ p1) → p4) → ((p4 ∧ (p4 ∨ (p2 → (False → p2)))) ∨ ((p1 → p5) ∨ ((((True → p3) ∧ False) ∧ p5) ∨ (True ∨ p2))))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310489498587306862759288681670 : (p2 ∨ (((False ∧ ((p1 → p2) ∨ p4)) ∨ p1) ∨ (False → (((False → ((True ∨ ((p1 ∨ False) ∨ p5)) ∨ (p3 → p4))) ∨ p4) → (p1 → p5))))) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320538891990074333997512091177 : (p4 ∨ (True ∧ ((p1 ∨ False) → (((((p2 ∧ (((False → p2) → (p2 ∧ True)) → p2)) ∧ ((True ∧ p3) ∨ (p3 ∧ True))) ∨ False) → False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_149060590241375367346146090191 : ((((False ∨ p1) ∧ p1) → (((((False ∧ p5) ∧ p5) → ((False ∧ p3) ∧ ((True → p3) → p3))) → p4) ∧ True)) ∨ (p2 ∨ (True ∨ (p4 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893191449765399510574131357347 : (((((True ∨ (True → ((p4 → ((p4 ∨ p2) ∧ (True ∧ p2))) → False))) → ((p1 → (False ∨ (p5 → True))) ∧ False)) ∧ ((p3 ∨ False) → p3)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (True → ((p4 → ((p4 ∨ p2) ∧ (True ∧ p2))) → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310611254958856756627802488192 : (p2 ∨ ((((p3 ∧ p5) ∨ p2) ∨ p4) ∨ (False → (False ∧ (p2 ∨ (((p5 ∨ False) ∨ p3) ∧ ((p2 ∨ p2) ∨ (((p3 ∧ p1) → p2) ∨ True)))))))) := by
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
theorem thm_5_vars_346310634266846312628110381202 : (p3 → (((p4 ∧ (((p5 ∧ (((p3 ∧ (True ∧ (p1 ∨ True))) ∨ p1) → p2)) → (True → p1)) ∧ ((p2 ∨ p4) → p5))) → False) ∨ (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117824394521940758749376768696 : ((p4 ∧ (p2 ∧ ((p2 ∨ (p3 ∧ (p2 ∧ p3))) ∨ (p3 ∨ ((p5 ∨ False) ∧ ((((True ∧ (p5 ∧ p3)) ∧ False) ∨ False) → p3)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662639166428248269359788830414 : ((((((True ∧ p3) → (p4 ∨ p4)) ∧ (((((p1 ∧ ((p1 ∨ False) ∧ (True ∨ p5))) ∨ (True ∨ False)) → p2) ∨ True) → p3)) → (p3 ∨ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 ∧ ((p1 ∨ False) ∧ (True ∨ p5))) ∨ (True ∨ False)) → p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633703564000882465960146726918 : (((((p5 ∧ ((((p5 → p1) ∧ ((((p4 ∨ (p5 → p4)) → (p2 → p5)) ∧ (p3 ∨ p2)) ∨ p3)) ∨ p3) ∨ p4)) ∨ (p4 → p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45917927525633431752019181583 : (((p4 → (((p3 ∧ False) ∧ p2) ∧ ((p5 → (p1 ∧ (False ∨ p1))) → ((p4 → (p1 ∧ ((True ∨ False) ∧ (p3 ∨ False)))) → p1)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350824602195306342970450207105 : (p4 → (((((p5 → (p4 ∧ (p5 ∧ p1))) ∧ (((True → (p1 ∨ p2)) ∨ (p1 ∨ p1)) → (p2 → False))) ∨ p5) → (p1 → p1)) ∧ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219218687456325113731721348398 : ((p1 ∨ ((p1 ∧ False) ∧ p2)) → ((((p2 ∧ (True ∧ ((p3 ∧ (p1 → p1)) → p2))) ∧ ((p2 → ((p4 ∨ p3) → p5)) → p2)) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232870827124828826554485439742 : ((p2 ∧ (p3 → p5)) → (((p2 → p4) ∧ p1) ∨ (((p4 ∨ (p5 → True)) ∨ p4) ∨ ((p4 ∨ ((p4 ∧ True) ∨ p3)) → (p4 → (p1 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136381823361153119373679044471 : ((((p2 ∧ p3) ∨ (p2 ∧ p1)) ∨ ((p3 → ((p2 ∨ True) ∨ ((p4 ∧ p3) → (p3 ∧ p2)))) ∧ (True ∧ (False ∨ False)))) ∨ (p3 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63978866022225229862073089065 : ((False ∨ (((((p3 ∨ ((p5 → (p2 ∨ p2)) ∧ False)) ∨ True) → p2) ∧ (p1 ∨ (False ∨ (p5 → ((False ∨ (True ∨ p2)) ∧ False))))) → p2)) ∨ p3) := by
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
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 ∨ ((p5 → (p2 ∨ p2)) ∧ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((p3 ∨ ((p5 → (p2 ∨ p2)) ∧ False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117381167569035601102991159917 : ((p1 ∧ (((((p5 ∨ True) ∨ p2) → ((False ∨ (((False → p3) ∧ ((p5 ∧ p1) → (p2 ∧ False))) ∧ False)) ∨ p1)) ∨ p2) ∧ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660429478758516749361612991332 : (((((((((p2 ∨ False) ∧ (p4 ∧ (p5 ∨ (((False ∧ (p1 → p4)) ∨ False) ∨ (p4 ∨ p2))))) → True) ∧ p2) ∧ True) → p2) → (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777687019875846603474251340320 : (((p1 ∨ ((((True ∧ p1) ∧ (p2 ∧ p5)) ∨ (p4 ∨ p4)) ∨ ((p2 → (p4 ∨ ((p3 ∨ (p4 ∨ False)) → (True ∨ (p1 ∨ False))))) ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137707936681878903879074786346 : ((p1 ∨ ((((((p2 → False) ∨ p4) → p2) → (p5 → p3)) ∧ False) ∨ ((p1 ∨ True) ∨ ((p4 ∨ (p4 ∧ p2)) → p3)))) ∨ ((p1 ∧ p3) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_161468951086153110566308542475 : ((p3 ∧ (((True → True) ∨ (((p4 ∧ False) → p4) ∨ p3)) → ((p2 → (p2 ∨ p5)) ∧ (p1 ∧ False)))) → ((p5 ∨ (False ∨ (p3 ∧ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → True) ∨ (((p4 ∧ False) → p4) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40497934696311539004848537894 : ((((True ∧ ((True ∧ p3) ∧ ((p2 ∨ (((p1 ∨ False) ∧ p2) ∧ p1)) → ((p4 ∧ (False → p5)) ∧ (p3 ∧ (False ∧ p5)))))) ∨ True) ∨ p5) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215433978911932263475886120684 : ((p3 ∧ ((True → p4) ∨ p4)) ∨ ((((((p2 ∨ ((p2 ∧ p4) ∧ p3)) ∨ False) ∧ p3) ∨ ((p5 ∧ p3) ∨ p1)) → p1) ∨ ((p5 ∧ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_139645897157867381920553423728 : (((((False ∨ False) ∧ (p3 → (p1 ∧ False))) ∨ ((p2 → ((p1 ∨ False) ∧ ((p2 ∧ p5) ∧ (False → p2)))) ∨ p2)) → p3) → (p1 → (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113438743440134471783843838144 : (((((p3 ∨ ((((p2 ∨ p4) → ((False ∨ p5) → p2)) → p5) ∨ p4)) → (p5 → ((True → False) ∨ True))) ∨ True) ∨ (p5 → p1)) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740189357714244591449534599361 : ((((False ∨ p4) ∨ (p1 → (p5 → ((p3 → True) ∧ ((((p1 → (p5 → (p2 ∧ p2))) → p4) ∧ ((p1 ∧ True) → (p4 ∧ p3))) ∨ True))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51099769382575656403863597724 : ((((((p3 ∨ p3) → True) → ((p1 → (p4 ∧ (True → (p4 ∧ (p5 ∨ False))))) → False)) ∧ p2) ∨ ((((p1 → False) → p4) ∧ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66416461560643973308053886152 : ((p5 ∨ (p3 → ((p1 ∧ ((((p3 → ((True ∧ (p1 ∧ p4)) ∨ (True ∧ False))) ∧ p4) → ((True ∨ p4) ∧ False)) ∨ p4)) ∨ (p1 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67678927009906809103229929764 : ((p1 → (p1 → (((((p4 ∨ ((((True ∨ True) ∨ False) → p1) ∧ (p5 ∧ p4))) ∨ p5) ∧ p3) ∨ (p3 → ((p2 ∨ True) ∨ True))) ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699240522714557669013292595604 : ((((p4 → (p4 ∧ (p4 → ((p1 ∨ (p1 ∨ (False ∨ p4))) ∧ p3)))) ∨ (p3 ∧ (((False ∨ ((p2 ∧ False) → True)) ∨ (False ∨ p4)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134005395648140296116797212858 : ((((p1 ∧ ((p5 ∧ ((((p2 ∧ p5) ∨ False) ∨ ((p4 ∧ (p3 → p3)) ∨ p5)) → p4)) ∨ (p2 ∧ p3))) ∧ p4) ∨ True) ∨ (p1 → (p2 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46010468288679438550787038734 : (((((((False ∨ (p3 → ((p1 → False) → p5))) ∧ False) ∨ p5) ∨ ((False → True) ∨ (p1 → (p5 ∧ (p2 → True))))) ∧ p2) ∧ (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671669800641167112882215974289 : ((((((p4 ∨ (p3 → ((((p1 ∧ p5) → ((True ∨ (p5 → p3)) ∨ p3)) ∨ (True ∨ p1)) ∨ p5))) ∨ p4) ∧ True) → ((p1 ∨ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66660908611718885676992755570 : ((True → (((True ∧ (p2 ∨ p1)) ∧ ((True → p5) ∧ p4)) → (p5 ∧ ((p2 ∨ ((((p3 ∨ p5) → (p3 → False)) ∧ p2) ∧ p1)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152090411289820369562498232467 : ((((p5 ∧ (p1 → ((False ∨ p2) ∧ True))) → (p5 ∨ p1)) → ((p1 → p3) ∧ (p3 ∧ ((True ∨ p2) → False)))) → (((p4 → p5) → p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (p1 → ((False ∨ p2) ∧ True))) → (p5 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47403877750480918613081018028 : (((True ∧ (p5 ∧ (p5 → ((p1 ∨ (((((p2 ∨ p4) ∧ False) ∧ (p4 ∨ p2)) ∧ (p4 ∨ (p1 → True))) ∧ True)) ∧ p4)))) ∨ (False → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600825962016988978596685621367 : ((((False ∧ (p5 ∧ ((True ∨ (((False ∨ p5) → p5) ∨ (((True ∨ (p3 ∧ p4)) ∧ ((p5 → (False → p5)) ∨ p2)) ∨ p4))) → p1))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



