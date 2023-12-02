variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40126382943754187658344417126 : (((((((p4 ∨ p2) ∨ ((p4 ∨ p4) ∨ ((p4 ∧ (p5 ∨ True)) → p3))) ∧ (p5 ∨ (True → p2))) ∨ (p1 → (True ∨ True))) ∧ p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47214770324875749254666863639 : ((((p4 ∧ (((p4 ∧ (p1 ∧ (p1 ∧ p4))) ∧ False) → p1)) ∨ (p3 → (((p5 → ((True ∨ False) ∨ p4)) → False) ∧ True))) ∨ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304845856900174496236281249528 : (p1 ∨ (((((False → p5) → p5) ∧ (((p1 ∨ p3) ∧ False) ∨ (p1 → True))) ∧ (((p1 ∨ p3) → (p5 ∧ False)) ∨ (p5 → True))) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140260837667698466898957830863 : ((((((False → ((p1 ∧ True) ∧ (p4 ∧ (p5 ∨ True)))) → p3) ∨ (True → (False ∧ p1))) ∨ p1) ∧ (p3 ∧ (False → p4))) → (p3 ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126317536824731824868877209919 : ((p1 ∧ ((p4 → ((((p3 → ((True → p1) ∧ p3)) ∧ p5) ∨ (p3 ∨ (p5 ∨ p3))) ∧ (p4 → (False ∧ (p4 ∨ p2))))) ∧ p4)) → (False ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218681872397630455821944564350 : ((True ∧ (p1 → (p1 → p2))) → (((p2 ∨ p3) ∧ ((p4 → True) ∧ (p5 ∨ p4))) ∨ ((((((True → p5) ∨ p4) ∧ True) ∨ True) ∨ p2) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49247655478894693592387732165 : ((((p5 → p2) → ((((p3 ∨ False) ∧ ((p1 ∧ p3) → p5)) ∨ p2) → ((p1 → ((p4 → p4) ∨ False)) → p3))) ∨ ((p4 → False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40495163715293917718742164625 : (((((p4 → p4) → (((p2 ∧ (((((p1 ∨ p3) ∧ p3) ∧ p2) → p1) → (p4 ∧ p3))) ∧ (p3 ∧ True)) ∨ (p2 → True))) ∨ p3) ∨ p5) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329336548467730560462855467452 : (True → (((True ∨ p1) ∨ p5) → (p5 ∨ ((((False → p4) ∧ p4) → ((p3 → p2) ∨ True)) ∨ (p3 ∧ (((p1 ∨ False) ∨ False) ∨ (p1 ∧ False))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165220672158277720945870878348 : (((((p2 ∧ (False → False)) ∧ (p1 ∨ p3)) ∨ ((p4 ∧ (p3 ∨ True)) → p2)) ∨ (p1 ∨ True)) ∨ (p4 ∧ (p3 ∧ (p4 → ((p5 ∧ p5) ∧ p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64968500824534239488004517593 : ((p2 ∨ ((p5 ∧ (p1 ∧ ((p1 ∨ p5) ∨ False))) ∨ ((False → ((p2 ∧ (((p1 ∧ (p5 → False)) → (p5 ∧ p5)) ∧ p4)) → True)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186296481402485299949317502182 : ((((p2 ∧ (p4 → ((p3 → (p5 → False)) ∧ True))) → p2) → False) → (p4 ∨ ((True ∧ p3) ∧ (p5 ∨ (True ∧ ((p4 ∧ (p4 → p1)) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p4 → ((p3 → (p5 → False)) ∧ True))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51747417431044435802135247198 : ((((True → (p3 ∨ p4)) → (((p2 ∨ p5) ∧ p1) → (True ∨ (False → (p1 → False))))) ∧ ((p2 ∧ p2) ∨ (((p3 ∨ p2) ∧ True) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672099808661318097142888592591 : (((((((p1 ∧ p2) → p5) ∧ ((True ∧ p1) ∨ (p1 ∧ (p4 ∧ (((False → True) ∨ p1) ∧ (p1 → p1)))))) ∨ p3) → ((True → p5) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686669160010021015361099994008 : (((((p5 ∨ p3) → ((False ∧ p4) → (((p2 → p5) → p3) ∨ (((p4 ∨ True) ∧ False) ∨ p2)))) → (p2 ∨ (p1 ∧ (p3 ∧ (True ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48964498924994414602750036150 : (((((((((p4 ∨ p4) ∧ False) → ((p5 → p3) ∨ ((True → (p4 ∨ p2)) → False))) ∨ p1) → p5) ∨ False) ∨ p1) ∨ (True ∨ (p3 → p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136706491331819069833890020318 : (((p1 ∧ p5) ∧ ((p1 → ((p2 ∧ (((p4 → (p4 ∨ True)) ∨ (False → p2)) → p3)) ∧ (p2 ∧ p4))) ∧ (p3 ∨ p1))) ∨ (False → (p2 ∧ False))) := by
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
theorem thm_5_vars_102789700816494745739947620847 : ((((((p5 ∧ (p1 ∨ (True → True))) ∨ (True → p1)) → (((p5 ∨ (True ∨ (p3 → p4))) → False) ∧ (p5 → p2))) → False) ∨ True) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165623456295671732179971362755 : ((((p3 ∧ (p3 ∨ (p5 ∧ p3))) ∨ p3) ∧ (((True → ((p1 ∧ p3) ∨ False)) → p2) → False)) ∨ (((p1 ∨ p2) ∧ (False ∧ False)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655740382076750553577333100412 : ((((((((p3 → True) ∨ True) ∧ ((((p1 → False) ∧ (True ∨ (p5 → p5))) ∨ p1) → p4)) ∨ p2) ∨ ((p1 → p1) ∧ p4)) ∨ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181455113078950551440154898936 : ((p3 ∨ (p2 → (((p5 → ((False → (False ∧ p5)) ∧ p2)) ∧ False) ∧ p2))) → ((((p5 ∨ p4) ∨ p1) ∨ (((True ∨ False) ∨ True) ∨ p4)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_41948185203613506023117169 : ((p4 ∧ p3) ∨ (((p5 ∨ p1) ∧ ((p5 ∧ ((p4 ∧ p4) ∨ (p1 ∧ p1))) ∧ False)) ∨ (p2 → (True ∨ (p1 ∧ (p2 → p5)))))) := by
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
theorem thm_5_vars_301612430363421200346765378763 : (False ∨ (((p5 ∨ p1) → p5) → (((p2 → (True ∧ ((True ∨ p5) ∨ (p4 → True)))) → (p2 → (p1 ∧ False))) → ((p4 ∨ p3) → (p2 → False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → (True ∧ ((True ∨ p5) ∨ (p4 → True)))) := by
      -- Implications on the right can always be decomposed.
      intro h7
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p2 → (True ∧ ((True ∨ p5) ∨ (p4 → True)))) := by
      -- Implications on the right can always be decomposed.
      intro h14
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687389112573935476208832402578 : ((((((((p3 ∧ (((p4 → p5) ∧ (p4 → p2)) ∨ True)) ∧ p3) ∧ p2) ∨ p4) ∨ False) ∧ (False ∧ ((((True ∧ p3) → p2) → False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186924012540847663618990607856 : (((p1 ∧ (False ∨ p4)) ∧ (p5 ∧ (p3 ∧ (False → (p4 → p4))))) → ((((True → p2) → (p5 ∨ (p1 ∨ (p4 ∨ False)))) → p2) ∨ (True ∧ p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326283020821505539602250497771 : (p5 ∨ (p4 → ((p5 ∧ (True → ((p3 ∧ (p5 ∨ p4)) ∨ (((False ∧ (p5 ∧ ((p3 ∧ p4) ∨ (False ∧ p1)))) ∧ (p4 → p1)) ∧ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190042070925942328904462858643 : (((((p4 ∨ (p5 ∧ p1)) ∨ (p3 ∨ True)) ∨ p5) ∧ p4) ∨ (p1 ∨ ((p1 ∧ (True → p2)) → (p1 ∨ ((p4 ∨ p2) ∧ ((p1 ∧ p5) ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209026629243292574492542252237 : ((False ∨ (p3 ∨ ((True → p5) ∨ p1))) → (True ∧ (p5 → (((p4 → True) → (True → False)) ∨ ((p2 ∧ p2) → ((p4 ∨ p3) ∨ (p3 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766449489902138214962625192903 : (((p4 ∧ (p1 ∧ ((True ∧ (False ∨ (((p5 ∨ p2) ∧ (False → p2)) ∨ p3))) ∧ ((((p4 → (p1 ∧ p4)) ∨ (p1 ∨ p1)) ∨ p3) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243958620947941689707987315987 : ((True ∧ p1) ∨ ((((p3 → (((p1 → ((((p2 → p4) ∨ p3) ∨ True) → False)) ∧ ((True → p5) ∨ p3)) ∨ True)) → False) ∧ p4) → (False ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (((p1 → ((((p2 → p4) ∨ p3) ∨ True) → False)) ∧ ((True → p5) ∨ p3)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p3 → (((p1 → ((((p2 → p4) ∨ p3) ∨ True) → False)) ∧ ((True → p5) ∨ p3)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60415762593559606414696934811 : (((p4 → p1) → (((p5 → (False → p5)) → p4) ∨ ((True ∧ (False ∨ ((p3 ∧ p1) → (p1 ∧ ((p1 ∧ p2) ∧ True))))) → (p1 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620222440975534879005766620224 : (((((p4 ∧ p2) ∨ (p4 → (p1 ∨ (p1 ∧ (p4 → (((False → True) ∧ ((p3 → (False → ((False ∧ p5) ∨ p1))) ∧ False)) ∨ False)))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_256590088857924239501315645983 : ((p1 ∨ True) → ((False ∨ ((((p1 ∧ (p2 → False)) → p1) → (False ∧ True)) → (p3 ∨ (p5 ∨ ((p3 ∧ (False ∨ p2)) → p5))))) ∨ (False → p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732941486082552974937030427211 : ((((p2 ∧ p2) ∧ (p5 ∧ (True → ((((p5 ∨ (False ∧ ((((p3 → ((p1 → True) → p3)) → False) ∧ p1) ∧ p2))) ∨ True) → p2) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708653379706747334551031363317 : (((((((p3 ∧ False) ∧ (p1 ∨ False)) ∧ p2) → p1) → ((((((p5 ∧ (p2 ∧ p4)) → p2) ∧ (p4 → (p4 ∨ p1))) ∨ True) → p5) → p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p5 ∧ (p2 ∧ p4)) → p2) ∧ (p4 → (p4 ∨ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321536344826776475778961857775 : (p4 ∨ (p2 → (((((((((p1 ∨ p3) ∧ p1) ∨ ((p5 ∨ True) → p3)) ∧ p3) ∨ True) → False) ∧ p3) → (p4 ∧ ((p4 ∨ True) → p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173516207092905109863047788536 : ((((p5 ∨ ((((True → p2) ∨ p5) ∨ p2) ∨ (False ∨ p4))) → (p1 ∨ p5)) ∧ p2) → (p5 ∨ (p1 ∧ ((True ∧ (p3 → (p1 ∨ p2))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ ((((True → p2) ∨ p5) ∨ p2) ∨ (False ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783844355794400052093273346777 : (((p3 ∨ (((p1 ∧ False) ∧ p1) ∧ (False ∧ (((p5 ∨ (p4 → ((p2 ∧ p1) → p4))) → p2) → (((False ∨ p1) ∨ True) ∧ (p5 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228065904529496998663426595343 : ((p4 ∧ (p3 ∧ p2)) ∨ (((p4 ∧ True) ∧ ((False → (((p3 ∧ (((p4 ∨ p2) ∨ False) ∨ p2)) ∨ p5) ∨ (p3 ∧ p4))) → (p3 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892231730710074639052237051815 : (((((p2 ∨ (p4 ∧ ((((False → p4) ∨ (p3 → p3)) → True) ∧ ((True → ((False ∨ True) → p2)) ∧ p1)))) ∨ p3) ∧ ((p3 ∨ p2) → p2)) → p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (False ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637870725814449293426775164657 : ((((((False ∨ ((p2 ∧ p3) ∨ p5)) → (p2 ∨ False)) ∧ ((p5 ∧ p1) ∧ (((p4 ∧ ((p2 ∧ (p1 → p2)) ∧ p4)) → p2) ∧ p2))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731559410606222728317772386647 : ((((False → (False → p3)) → ((((((p5 ∨ p4) ∨ False) ∨ p2) ∧ p2) → True) ∧ ((True → ((p1 → p3) → ((False → p5) → p5))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49037135343964630948707819043 : ((((p3 ∧ (p4 ∨ (p4 ∨ (p2 ∨ ((((p2 → (False ∧ False)) → (p3 ∨ p1)) ∨ p3) ∨ (True ∨ True)))))) → False) ∨ ((p3 → True) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307378488802189499436817199646 : (p1 ∨ (p4 ∨ ((((False ∨ (p4 ∨ p4)) → (p1 ∨ False)) ∨ (p1 ∨ (((p4 ∨ ((p2 ∨ p2) ∨ p4)) ∨ p1) ∨ True))) ∨ (p3 ∧ (p5 ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730149818204681925546998118351 : (((((p5 ∨ p1) → p5) → ((False ∧ p4) ∨ (p2 ∨ ((True → (False → p5)) → ((p5 ∧ p1) ∨ (False → ((p5 → p1) → (p2 ∧ p4)))))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300862735786856272293506962717 : (False ∨ ((p3 → (p5 ∨ ((p5 ∧ ((((False ∧ p5) → p3) → p4) ∨ p4)) ∨ p3))) ∧ (True ∨ (False → (((p5 ∨ True) ∧ (p3 ∧ p3)) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56444958606676460151191568757 : ((((True ∨ p3) ∨ (False ∧ p5)) → (True → ((p3 ∧ (((False ∨ True) → p5) ∧ ((False ∨ (False → True)) ∨ p1))) → (p4 → (p2 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305163632017086411987876373377 : (p1 ∨ (((((p4 ∧ ((((p5 ∧ p3) ∧ p2) → ((p5 ∨ p4) ∧ p1)) ∨ p2)) ∧ (p3 ∧ p2)) → p2) → False) ∨ ((p1 → (p1 ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611020914197316667109048003902 : ((((((p3 ∨ (((p1 → False) → False) → p5)) ∧ (((((False ∧ p3) → (p3 → ((False ∨ p4) → p2))) ∧ p4) ∧ p1) ∨ p3)) → p2) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603545636102065221842925939438 : ((((p3 ∨ ((p4 ∧ p2) ∨ (((p1 ∧ ((p5 ∧ p5) → (p1 ∧ p1))) ∨ ((p4 → False) ∨ (True ∧ p1))) → (p5 → (True → p2))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58442419597778206968185416453 : (((p3 ∨ False) ∧ ((p1 ∧ p4) ∧ ((((((False → p3) ∨ p1) ∨ p3) → ((p5 → (p4 ∧ p4)) ∧ True)) → (p4 ∧ (p1 ∧ p3))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133896523420208002895430257443 : (((False ∨ (p1 ∧ (((((p5 → ((p3 ∨ (False ∧ p5)) ∨ True)) ∨ (p2 ∧ p2)) ∨ p3) ∧ p4) ∨ (p4 → p2)))) ∧ False) ∨ ((True ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44560897899315441314453331839 : (((((p1 ∨ True) ∧ (True ∨ (p2 ∧ (p3 ∨ False)))) ∧ ((((True ∧ p3) → ((((True → p3) ∨ p4) → p4) → p2)) ∨ True) → p2)) → p2) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (((True ∧ p3) → ((((True → p3) ∨ p4) → p4) → p2)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (((True ∧ p3) → ((((True → p3) ∨ p4) → p4) → p2)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785344760115964464872416394070 : (((p4 ∨ ((((False ∧ ((p1 ∧ ((p1 → p2) ∨ ((p4 ∧ p3) ∧ (p3 → p2)))) ∧ p4)) ∨ (((True → p4) ∨ True) ∨ p1)) ∨ p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179146085216138106559190470601 : ((p2 ∧ (((p3 → ((p3 → ((p2 ∧ False) → True)) → p5)) ∧ True) ∧ p2)) ∨ (p4 ∨ (p2 ∨ (((False ∨ p4) → (True ∨ p4)) ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_177749699506655548646451024177 : ((((p2 ∨ p3) ∧ ((p1 ∨ False) ∨ ((p5 ∨ p1) ∧ (p3 ∨ False)))) ∧ p4) ∨ (((p1 ∨ (False ∨ p3)) ∧ (p1 → p3)) → (p5 → (p2 → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157802739682201020103333083530 : (((p3 → ((True ∧ (True ∨ (((p5 ∨ False) → p4) ∧ p1))) → p5)) ∨ (((p5 ∧ False) ∨ p1) ∨ False)) ∨ (((p1 → (p5 ∧ p3)) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46404188327197780689524047896 : (((((False ∨ ((p3 → p2) ∨ (p3 ∨ p3))) ∨ p3) ∨ (p1 → ((((True → False) ∨ p3) ∧ (p4 ∧ p3)) ∨ (p5 → p3)))) ∧ (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164202186365346409149200432430 : ((p5 ∨ ((p5 ∧ p1) ∨ (p5 ∨ ((((p1 → p5) ∨ False) → (p2 ∨ p5)) → (False → False))))) ∧ (((True → p2) ∧ p4) ∨ ((True ∨ p3) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321016059224814417370753946465 : (p4 ∨ (False ∨ (((p5 → (p3 ∨ p4)) → (p3 ∧ p1)) → ((((True → (p2 ∨ p1)) ∨ False) → (p5 → True)) ∧ ((True ∧ (p4 ∨ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p5 → (p3 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262377455199138929319754600082 : (True ∧ (((p4 ∨ p5) ∧ ((p4 ∧ (((((p3 ∨ p4) ∨ ((p5 ∨ (p2 ∧ False)) ∧ p3)) → ((False ∧ p2) ∧ p5)) → p4) ∧ p3)) ∨ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300766730910312377354080560097 : (False ∨ ((p1 → ((p1 ∨ p5) ∧ (p2 → (((p3 ∨ (True ∨ p4)) → (p2 ∧ p4)) ∨ p2)))) ∧ (((p4 ∧ (p2 → p1)) ∨ (p5 ∨ True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47516617727624647995451887464 : (((p3 ∨ (((((p4 → (True ∧ ((True → (p4 ∨ p2)) ∧ p1))) ∨ False) → p1) ∨ (p5 ∨ (False → (False → p3)))) ∧ p5)) ∨ (True ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91746438929452066341734148042 : (((True → False) ∨ ((((True ∧ p1) ∨ (p3 ∨ (True ∧ (p4 ∨ (p3 ∨ (False → ((False → p2) ∧ p3))))))) → (False ∨ p3)) ∧ (p2 → p4))) → p3) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((True ∧ p1) ∨ (p3 ∨ (True ∧ (p4 ∨ (p3 ∨ (False → ((False → p2) ∧ p3))))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h8
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47583044779001366289472437146 : (((p2 → ((True ∧ (((p5 ∧ (p1 ∧ (True → (False ∧ p1)))) ∨ (True ∨ p2)) ∧ (p1 → (p3 ∨ (True → p5))))) ∧ p3)) ∨ (False → p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258808696986808466092724854310 : ((True → False) → (p2 ∨ (((True ∧ p4) ∨ ((((p5 ∧ (p4 ∧ (p4 ∧ True))) → False) → (p5 → (((p3 → False) ∨ p2) → False))) → p2)) → p4))) := by
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
theorem thm_5_vars_76193844855271995864790587135 : ((((((p2 ∧ ((((p2 ∧ (p5 ∨ p1)) ∨ True) → p1) ∧ ((p1 ∨ False) ∨ ((True ∧ True) ∧ p5)))) ∨ True) ∨ p1) ∧ (True ∧ True)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ ((((p2 ∧ (p5 ∨ p1)) ∨ True) → p1) ∧ ((p1 ∨ False) ∨ ((True ∧ True) ∧ p5)))) ∨ True) ∨ p1) ∧ (True ∧ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244313108059852596449760764157 : ((False ∧ False) ∨ ((p5 ∧ ((p5 ∨ (p1 ∧ p5)) → ((((((True ∨ (False → p3)) → p3) ∧ (p5 ∨ True)) → (p4 ∧ p2)) ∧ p4) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356532651532146546666298489780 : (p5 → ((((p1 ∨ True) → (True ∨ p4)) → (p1 → (p2 ∨ False))) ∨ (((True → False) ∧ p1) → ((True → p2) ∨ (p2 ∨ (p3 ∧ (True ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181075419330438203165492104375 : (((p2 ∨ p5) → (((False → p5) ∨ (p5 → ((p1 ∨ p5) ∧ p4))) ∨ p4)) → ((p1 ∧ (p5 ∨ p4)) ∨ ((p3 → ((True ∨ p2) ∨ p1)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115171121091953324871016635567 : ((((p3 ∧ (p5 ∧ (p3 ∨ (True ∨ (p5 ∧ p1))))) ∨ True) ∧ ((((p3 ∧ (p1 → ((p1 ∨ p3) → True))) ∨ True) → p4) ∨ False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337373639331404674683660726494 : (p1 → ((((False ∧ (p5 ∧ p2)) ∧ True) ∨ ((((p4 ∨ (p4 → (False → p2))) → p5) ∨ ((p2 ∧ p1) ∧ p4)) → p3)) ∨ ((p4 ∨ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119219587867335659033374972724 : ((p2 → ((p3 ∨ (p3 ∧ (True → p4))) ∨ (p2 ∧ (p3 ∨ (p2 ∧ ((((p2 ∧ True) → False) ∧ (False ∨ p2)) ∨ (p4 ∨ p2))))))) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183936523580912088857218816413 : (((False ∨ (((((p1 ∧ p3) ∨ False) ∧ p3) ∧ p3) ∧ True)) ∧ p2) ∨ (False → (p1 ∨ (p1 ∧ (((False ∨ ((p1 ∧ False) ∨ p1)) ∨ p4) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41683640452640948151388550995 : ((((p5 ∧ ((True ∧ p3) ∨ (p5 ∨ p1))) ∨ ((p1 ∧ True) → ((p3 ∨ (True ∨ p5)) → ((p5 ∧ (p5 → p3)) ∧ (False → p3))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694554007383677665908038797610 : ((((p2 ∧ (((False ∨ (p1 ∨ (((p2 ∧ p1) ∧ p4) → p1))) → p1) ∨ p1)) ∨ (((False → p5) ∧ (False → ((p5 → p3) ∧ p4))) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356518877472002759535619498473 : (p5 → (((((False → True) ∧ ((p4 → p4) → p2)) → p4) ∧ True) ∨ (((p3 → (p3 → ((p2 ∧ False) → ((True ∧ p1) ∨ False)))) ∨ p4) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241377852617734028924573959472 : ((False → False) ∧ (False ∨ ((((((p5 ∧ p2) ∨ (p3 ∨ p5)) ∨ True) ∨ p3) ∨ (False ∨ p2)) ∨ (((False ∧ True) ∧ p3) ∧ (False ∧ (p2 → p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151174261702420884771236286498 : ((((False ∨ (((p1 → (False ∨ p1)) → (p4 ∧ p2)) ∧ (p1 ∨ p5))) → ((p2 ∧ (False → p4)) ∧ True)) → p2) → (p3 ∨ (False ∨ (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (((p1 → (False ∨ p1)) → (p4 ∧ p2)) ∧ (p1 ∨ p5))) → ((p2 ∧ (False → p4)) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h10 : (p1 → (False ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h12 := h7 h10
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : (p1 → (False ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h17 := h7 h15
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- False on the left can always be used.
    apply False.elim h19
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609004463092730241310476136063 : ((((((((True ∨ ((p2 ∨ p3) ∧ (False ∧ p3))) → p3) → p4) ∨ ((((p5 → True) → (p5 → False)) ∨ p3) ∧ (p5 ∨ True))) ∨ True) ∨ p3) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_248439130523114544226285922087 : ((p2 ∨ p5) ∨ (((p5 ∧ (p4 ∨ ((p3 ∨ ((((p2 ∨ p2) → ((p5 ∨ p4) → True)) ∨ p1) → ((False ∨ p1) → p3))) ∨ p4))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69172996302339684990851214125 : ((p5 → ((((p5 ∧ ((p3 → ((p4 ∨ (p4 → p4)) → p5)) → (False ∨ p1))) → p4) ∨ p5) → (p3 ∨ (((p2 → p3) → p4) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63185793667111649832400578301 : ((p5 ∧ (((p1 ∨ True) ∧ ((p2 ∧ (p3 ∨ p3)) → (((((p5 ∨ p3) ∧ p4) ∨ (False ∨ p5)) ∧ p3) → False))) ∧ (False ∧ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93099467299257385442953384119 : ((True ∧ (((p1 → False) → p2) ∧ ((((((p2 ∨ ((p1 ∨ False) ∧ (p2 → p4))) ∨ p3) ∨ (p3 → (p3 ∧ True))) ∨ p2) ∨ p5) → p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((p2 ∨ ((p1 ∨ False) ∧ (p2 → p4))) ∨ p3) ∨ (p3 → (p3 ∧ True))) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664379551278291574244087518782 : ((((p3 ∨ (((((p3 ∨ p2) ∧ ((p1 → (p1 ∨ p3)) → (p2 → p4))) ∨ ((p2 → False) ∧ p1)) ∧ (p5 ∨ p4)) → p5)) → (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685423539625351972155861108 : ((((p4 ∨ ((p3 ∧ p1) ∨ (p3 ∧ p1))) → ((p2 ∨ p1) ∧ (True → p5))) ∨ ((False → True) → (p1 ∧ ((p4 ∨ p4) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260551747287897557560071918659 : ((p3 → p1) → ((p5 ∨ (True → (False ∨ (p5 ∨ p5)))) ∨ (p5 ∨ (True ∨ ((((p5 → (p2 ∨ p3)) ∨ (p1 ∧ (False ∧ p3))) → p4) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152094529012978924912962387651 : ((((p3 → (p5 → True)) ∨ (((p1 → False) ∨ p3) ∧ p1)) → (((p5 ∧ p5) ∨ ((p1 ∧ p2) ∧ p3)) ∧ p1)) → (((p5 ∨ p2) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786926817479461935931023396391 : (((p4 ∨ (((p1 → p2) → p3) → (p2 → ((p2 ∨ (((True → (p1 ∧ True)) ∧ (p1 → p3)) ∨ False)) ∧ ((p5 → (p5 ∧ p5)) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679733243357893006085333393458 : ((((((p3 → ((True → ((p4 ∨ p5) ∨ ((True ∨ p3) → (True → True)))) ∨ p2)) → (p2 → p4)) ∨ True) → ((True ∧ False) ∧ (p2 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199908119952736681945141047574 : (((((p2 ∨ p3) → False) → p1) ∨ (True → p1)) → ((p3 → p3) ∧ (((p5 → ((p3 ∧ p4) → (False → ((p2 → p4) → p4)))) → p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p5 → ((p3 ∧ p4) → (False → ((p2 → p4) → p4)))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : (p5 → ((p3 ∧ p4) → (False → ((p2 → p4) → p4)))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- False on the left can always be used.
      apply False.elim h17
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h14
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114923260852053328492950065270 : ((((p1 → (p4 ∧ (((p5 ∧ p3) → ((True ∨ p5) ∨ p5)) ∨ p3))) → True) → ((p2 ∧ (((p4 ∨ p2) ∧ p2) ∧ p4)) → p4)) ∨ (p1 ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190330930387433247576307267411 : (((((p2 ∧ True) ∨ (p2 → True)) → (p1 ∨ False)) ∨ False) ∨ (((p1 ∨ (p1 ∧ (p4 ∨ True))) → (True ∨ (((p3 ∨ p5) → False) ∧ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37165120517579791842033157642 : ((((((False ∧ (p5 ∨ False)) ∨ (((p3 → p2) ∨ (p3 ∧ (p2 ∨ False))) ∨ (p3 → False))) → (p5 ∧ (p2 ∨ (p3 ∧ p3)))) ∧ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37846403769661247683945687889 : ((((p5 ∨ (p4 ∨ (True → (((p2 → ((p2 → p2) → (False → p1))) → (p3 ∨ ((p2 ∧ (p5 → False)) → p5))) → p4)))) → False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345666344912783967848498228069 : (p3 → ((False ∨ ((((((False ∨ (p3 ∨ p1)) ∨ p2) ∨ False) ∨ False) ∨ False) ∧ (((((p1 → p5) ∧ p5) ∧ p4) ∨ (p1 → p5)) → p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345754228811404745078767016526 : (p3 → ((((p1 → (((p2 ∧ p3) → (((True → p3) ∧ p1) ∧ p5)) → (True ∧ p3))) ∧ (((True → p1) ∨ True) → (p1 ∧ False))) ∧ p5) → p4)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((True → p1) ∨ True) := by
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
theorem thm_5_vars_51165959552521268135126924848 : ((((p4 ∧ ((p5 ∧ (p1 ∨ (p3 ∨ p2))) → (((p3 → True) → p4) ∨ p4))) ∧ (p2 → p3)) ∨ (((p1 ∨ p1) → (p1 ∧ p3)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172614329281498423579732777238 : (((p4 → (p1 → p1)) → (False ∨ (p2 ∧ (p4 ∧ (False → (p3 → (p4 ∧ True))))))) ∨ ((True → p1) → (True ∨ ((p5 → True) ∧ (False ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52884940809446767030728997549 : (((p1 ∨ ((True → (True ∧ (p5 ∧ p2))) ∨ (((p2 ∧ p2) ∨ p3) → p3))) → ((((p5 ∧ (True → True)) → p5) → p5) ∨ (True ∨ p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



