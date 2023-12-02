variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233923885968888117383389495877 : ((p4 ∨ (p2 → False)) → (((True → p2) ∧ ((False → p3) → (p1 ∨ p3))) ∨ ((p5 ∧ p1) ∨ (((False → p1) ∨ ((True ∨ True) ∧ False)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148932469859077547091930760615 : ((((p2 → p2) → (True → p2)) → (((((p2 ∧ p5) → p4) → ((p4 ∨ (p2 ∨ p3)) → p3)) ∨ p2) ∨ p4)) ∨ ((p1 ∨ (p1 ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114336050431122267005174787042 : (((p4 ∧ (((p2 ∨ p1) ∨ p5) → (((False → (p4 → (p2 ∧ True))) → p4) ∨ (False ∨ False)))) ∧ ((p4 ∨ (p2 → True)) → p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219717104332988439072505879185 : ((p1 → (p1 ∧ (p5 ∧ False))) → ((((((False ∧ p4) ∨ p5) ∧ (p2 ∨ p2)) ∨ p2) ∨ False) ∨ (True ∨ (((p4 ∨ p2) ∧ p4) → (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586089434898314207158704776363 : (((((((p1 ∧ ((False ∧ p2) ∨ ((p5 ∧ True) ∨ ((p3 ∨ p4) ∨ (p2 ∧ True))))) ∨ True) ∨ ((False ∨ (p4 ∨ True)) → p4)) ∧ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_984293086299516700934275132357 : (((p1 ∧ (False ∨ (((p1 → True) ∨ p4) → ((p1 ∧ ((p5 ∨ ((p3 ∧ ((p2 ∧ p1) → False)) ∨ True)) → ((p5 ∧ p5) → p5))) ∧ p2)))) → p2) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 → True) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206001399680229325764915316238 : ((p1 ∧ (p5 ∨ (True → (p1 ∨ p1)))) ∨ ((p3 ∨ (((True ∨ p5) → False) → (False ∧ p3))) ∨ ((((False ∧ True) ∧ True) → (p3 ∧ p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2079814072922058544914571620 : (((p1 ∨ ((p4 ∧ (False ∨ p3)) ∨ (False ∧ ((p3 ∨ False) → (False ∧ True))))) ∨ (p2 → p4)) ∨ (p2 → (False → (p4 ∧ (p5 → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810547493397219906492953054987 : (((p5 → (((p2 ∨ False) ∨ (p1 → False)) ∧ ((p1 ∧ ((p3 ∨ p4) → (p3 ∨ p3))) ∨ (p2 → (((True ∨ False) ∨ p1) → (p5 ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201219948142076865833628877836 : ((p2 → ((p4 → (p1 → False)) ∧ (p5 → True))) → ((((p3 ∨ (p4 ∨ (((p5 ∨ (p4 → False)) → (p2 ∨ p5)) ∨ p3))) ∨ p3) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342773147409227053735488242925 : (p2 → ((p4 → (p1 ∨ ((False ∨ (p3 ∨ p5)) → p1))) ∨ ((p5 → ((((((p4 → False) → p1) ∨ True) → False) ∨ p5) ∧ (p3 ∨ p2))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114646753932835115173415328709 : (((((False → False) → (p4 ∧ ((p5 → p4) → ((p1 → p4) → p4)))) → (p1 ∧ p1)) ∨ ((p3 ∨ (False → p4)) ∧ (p4 ∧ p2))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259273376994237386738538571323 : ((False → p1) → ((((p1 ∧ (p1 ∧ p2)) ∧ (p4 ∧ p4)) ∧ (p2 ∨ p4)) ∨ (p2 ∨ (True → ((p4 → (p5 → p1)) ∨ (True ∨ (False ∧ p3))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82414878935462193233949508595 : ((((p4 ∨ p1) ∧ (p2 ∨ (((((p5 ∨ p3) ∧ True) ∨ p2) → (((p4 ∨ False) ∨ True) → p2)) → p1))) ∧ ((True ∨ True) → (p2 ∧ False))) → p5) := by
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
      have h8 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h21 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177677055593935471121385787248 : (((((p2 → ((p1 → p4) ∧ p2)) → ((p3 ∨ p4) ∨ p5)) → p1) ∧ True) ∨ (True ∧ (p1 ∨ (((p1 ∧ (p4 ∨ False)) ∨ False) → (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47450400715859312922200229383 : (((p4 ∧ ((((p2 → (p5 → (((p5 ∧ ((p5 ∨ (p2 → p4)) ∨ p3)) ∨ p5) ∧ p5))) ∨ p2) → (p5 ∨ p2)) ∧ p2)) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194134489063708254170831120050 : ((p1 → ((p2 ∨ (p2 ∨ ((p1 ∨ p4) ∧ p1))) ∨ p1)) → ((p1 → (p4 ∧ True)) ∨ ((p2 ∨ (True ∧ (p3 → (p5 ∨ (True → True))))) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60653373345513955907315684451 : ((True ∧ ((p5 ∧ ((p3 ∨ (p2 ∧ (p3 ∨ (((p5 ∨ ((p5 ∧ False) → p5)) ∧ p3) ∧ p1)))) → False)) ∧ (p5 ∨ (True → (p3 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260453466149963991141071305079 : ((p3 → True) → (p1 → ((((p4 ∧ p2) ∨ True) ∧ (p5 → p4)) → (((p1 → (False ∧ (p3 → True))) → False) ∧ ((p4 ∨ False) ∨ (p1 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h3.left
  let h18 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65524533740962398535744827831 : ((p3 ∨ (p2 ∨ (True → ((((p5 ∨ (True ∧ p1)) ∨ ((False → ((((p1 ∨ p5) → p4) → False) ∧ p1)) → (p2 → True))) ∧ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65035132599158626850668005248 : ((p2 ∨ ((False → p1) → (((p4 ∨ (p1 ∨ p3)) ∧ p1) ∨ (p3 → (((p1 → (True → (p1 ∨ p2))) ∨ (p1 ∨ p3)) ∨ (p1 → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192047163379829702807880247797 : ((p2 → (True → ((True ∧ (p4 → p1)) ∨ (False ∧ False)))) ∨ (p2 ∨ ((p2 → ((p1 → True) ∧ (False ∧ p2))) ∨ ((p5 → (True → p2)) ∨ True)))) := by
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
theorem thm_5_vars_49799659888802770662580530743 : (((True → (((p2 ∨ p2) → ((((True ∧ (True ∧ False)) → (p2 ∧ p1)) ∨ (p2 → p3)) → (p1 → p2))) → p3)) → ((p5 ∧ p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40413033687012667117658646915 : (((((((False → ((p5 ∧ p1) → (p2 ∨ p1))) ∨ p2) → ((p2 ∧ (True ∨ True)) → p3)) ∨ ((p1 ∧ (False ∨ True)) ∨ p5)) ∨ p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42671792606390044949283861268 : (((p4 ∨ (True ∧ ((((p3 ∨ (p3 ∨ True)) ∨ False) → p3) ∧ (((p1 → p3) → (p4 ∧ ((True ∨ p3) → (p4 ∧ p1)))) ∨ False)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592790611684339678663690353094 : (((((((((True ∨ p4) ∧ (False ∧ p4)) → (p1 → True)) ∧ (p2 ∨ ((False → p1) → False))) ∨ (True → True)) ∧ ((p5 → p1) ∧ p1)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130120572868846085920985216753 : (((((p4 ∧ (p4 → ((((False ∨ p5) ∨ False) → (False → p1)) → p1))) ∨ p4) ∨ (True → (p3 ∧ p1))) ∨ (p1 → p1)) ∧ (False → (p4 ∨ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611136700984254302360550948250 : ((((((True ∧ (p4 → p1)) ∧ ((((((p5 → (p3 ∧ p3)) → True) → (p1 → p1)) → p5) → (p3 ∧ (False ∧ False))) → p4)) → p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65630054476745823803421158063 : ((p4 ∨ (((((p2 → False) ∨ (p1 ∨ p5)) ∧ (((p3 ∨ ((p4 → p4) → p1)) ∨ p3) → (((p2 ∨ p3) → p3) → p4))) → p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640159796190076667520550699486 : ((((((p3 → p2) ∨ False) → ((True ∧ (((p1 → ((False ∧ (((p3 ∨ p5) ∨ True) ∧ p4)) ∨ p2)) ∨ False) ∧ (p4 → p2))) → p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116377756025299393972573490249 : ((((False → p1) → p4) → (p1 → (((((p4 → (p4 ∧ p5)) → p2) ∧ p4) ∧ (True → ((p4 ∨ (p2 ∨ False)) ∧ p5))) → p5))) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39265472373411474412952426004 : (((False ∧ (p4 ∧ ((((p2 ∨ ((p4 → p1) → p4)) → ((False → p3) ∧ ((p3 ∨ p1) → p5))) ∧ (p1 → (True → True))) ∨ False))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607082304316701279933760830657 : (((((((p5 → False) → (True ∧ (p4 → ((p1 ∧ p4) ∧ p1)))) ∨ (p2 ∨ (p1 → ((p3 ∧ ((p5 ∨ True) ∨ p2)) ∨ p3)))) ∧ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114625573466733609308154610950 : ((((p2 → ((p1 ∨ p3) → (((p3 ∨ (True ∧ p3)) → (p4 ∨ p5)) ∧ p2))) ∧ p1) ∨ (False → (p4 ∨ ((True ∨ p3) ∨ p1)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703260258132339378618585591146 : ((((p2 ∧ (p2 → (p1 ∧ (p5 → (p4 ∧ (p2 → False)))))) ∨ ((False ∧ p3) ∨ ((p3 ∧ True) → ((False ∨ p3) ∨ ((p3 ∧ p3) ∧ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233736545771541494137694943537 : ((p3 ∨ (p3 ∧ p5)) → ((((((p1 ∧ True) → (p3 ∧ (p4 ∨ p1))) ∧ (((p1 → False) ∧ (p1 → p4)) ∨ p5)) → False) → p2) ∨ (p2 → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165514339186617791638141938332 : ((((p3 → (False ∧ (((p5 ∧ False) ∧ p4) ∧ False))) → True) → (True → ((False ∨ p5) → p4))) ∨ ((p1 ∨ (p3 → p2)) ∨ ((p2 ∧ p1) → p1))) := by
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
theorem thm_5_vars_797134853537455171266872751869 : (((p1 → ((True ∧ ((p3 ∨ (((True ∨ ((p3 → p1) ∨ p3)) → (((p2 → (p3 → True)) ∧ True) → True)) ∧ (p1 ∨ p1))) → p3)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932096217890904170614153728658 : ((((((False → p5) ∨ (p5 ∧ (p4 → p5))) → False) ∧ ((p1 ∧ (p3 ∧ ((((p5 ∧ p5) → (p2 → p1)) → (False ∧ p1)) ∨ True))) → p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False → p5) ∨ (p5 ∧ (p4 → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65442929548272617596152001720 : ((p3 ∨ ((p2 ∧ p1) ∨ ((p4 ∨ p3) ∨ (((p2 ∨ False) → ((p5 → (p1 → (p1 ∨ True))) ∧ (p1 ∨ p2))) → ((p4 → False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217150498051844928432619961085 : ((((p4 → p1) ∨ p2) ∨ p1) → (((p4 ∧ p3) ∨ (True ∨ (((p5 → (False ∧ (p4 ∧ False))) ∧ p3) ∧ p2))) ∨ ((False → True) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313138280575290906386824879707 : (p3 ∨ (((((p1 ∨ False) ∧ ((p5 ∨ (p5 ∧ True)) ∨ ((p2 ∧ p5) ∨ p4))) ∨ (p3 ∨ True)) ∨ (p5 ∧ ((p4 → p4) ∨ (p5 ∨ p5)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116091067450232582680091816377 : ((((p4 ∨ False) ∨ p5) ∧ (((p2 → p2) → p3) ∧ (p4 → (((p2 ∧ ((True ∧ False) ∧ (p2 → p3))) ∨ (True ∨ p5)) ∨ p2)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718812669150030878194802029671 : (((((p2 ∨ p5) ∨ (True ∧ False)) ∨ (False ∨ ((p2 ∨ ((((True → p3) ∧ p1) → (p5 ∧ True)) ∨ (True ∧ (p1 ∨ p3)))) ∨ (False → p5)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319541284833888792392966821688 : (p4 ∨ ((((((p4 ∧ p3) ∨ p2) ∧ False) → (False → p1)) → p5) ∨ (p2 ∨ (True ∧ ((((True → p5) ∧ False) → (p4 → p3)) ∨ (False ∧ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759404062380593390774236718474 : (((p2 ∧ (((p3 → (((((p3 → p5) → p3) ∧ ((False ∧ False) ∧ (p1 ∧ p4))) ∧ (p4 → p3)) ∧ p5)) ∨ p2) → (False ∨ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44507655108003406126514387765 : ((((((False ∨ p3) ∨ (((False ∨ p5) ∨ p4) ∧ False)) ∧ p4) ∨ (p2 ∨ ((((((p3 ∨ p1) ∧ p3) ∨ False) ∨ False) ∨ p5) → p2))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51077409929793178624999832995 : (((p4 → ((((p5 ∧ (False ∧ p5)) ∨ p4) ∨ ((False ∨ ((p1 ∧ p5) → p5)) ∨ p4)) ∧ p1)) ∧ (True ∧ (((p5 → p4) → p4) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156616442867628468917559722346 : ((((p5 → (((p4 ∨ (p2 ∧ ((p4 → ((p1 ∨ p5) ∨ True)) ∨ p4))) → True) → p4)) ∧ p2) ∧ p3) ∨ ((False → False) ∨ ((p1 ∧ p3) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813414372609370217915114939662 : (((((False ∨ (((((p2 ∨ (False → p5)) → False) ∧ (((p3 ∨ p5) → (p3 → (p3 ∨ p4))) ∧ p1)) → (False ∨ p5)) → p5)) ∧ p4) ∧ p4) → p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((((p2 ∨ (False → p5)) → False) ∧ (((p3 ∨ p5) → (p3 → (p3 ∨ p4))) ∧ p1)) → (False ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h14 : (p2 ∨ (False → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h16 := h10 h14
      -- False on the left can always be used.
      apply False.elim h16
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683602059914597313640521480368 : ((((((p1 ∧ (False → (p1 → (p3 → ((((p1 ∧ p1) ∨ False) ∧ False) ∧ True))))) → p3) ∧ True) ∨ (p5 ∧ ((p2 → (True → p1)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774708536731784546345770230159 : (((False ∨ ((((True → (p5 → False)) ∧ (p2 ∨ True)) → False) ∨ ((p2 ∧ ((p5 ∧ (p5 → (p5 ∧ ((p2 → p5) ∧ p5)))) → False)) → p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314760897363038378527914281647 : (p3 ∨ ((p1 → ((p4 ∨ (p1 ∨ p1)) → (p5 ∨ (p1 → (p2 ∧ (False ∨ p3)))))) ∨ ((False ∧ (p5 ∧ (True ∨ (p5 → (p1 ∨ p1))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_327012083729858780844959841718 : (True → ((((p3 ∨ p3) ∧ ((False ∨ (p4 ∨ (p4 → (p3 ∧ p3)))) ∧ ((p3 ∧ p1) ∨ p5))) → ((p4 ∨ (p5 → (p5 ∨ p1))) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753918284004941705864797846445 : (((False ∧ ((((False ∧ True) ∨ (p5 ∨ p5)) ∧ p3) ∧ (False → (p5 ∨ (p1 → (True ∨ ((((False → p5) ∨ (False ∧ False)) → p4) ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166274139562501235469267516131 : ((p3 ∧ (p2 → ((((p1 → p2) ∧ (p5 ∨ (p5 ∧ (p1 ∧ (p3 ∨ True))))) ∨ p5) ∧ p3))) ∨ (((False ∨ p5) → p3) → (True → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173647870601611919614216829087 : (((((((True ∧ p3) ∧ p3) ∨ (((p2 ∧ p3) → p2) ∧ True)) ∨ p1) ∧ p2) ∨ p3) → ((((True → p1) ∧ ((p5 ∧ p1) ∧ p4)) ∨ True) ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172728633576924447904632142007 : (((p1 → p4) ∨ (((p4 ∨ ((p3 → True) → p5)) → ((p4 ∨ p3) ∨ p3)) ∧ p3)) ∨ ((p2 → ((p1 → (True ∧ (p4 ∧ p1))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481758240598529714656314495773 : ((((p5 → (p4 ∨ ((False ∧ p5) ∧ (p4 ∨ p3)))) ∨ ((p2 ∧ ((p3 → ((p3 ∧ (p1 ∧ False)) ∧ (p3 ∧ True))) ∧ p4)) ∨ (p5 ∨ True))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_315154506672364031907392166568 : (p3 ∨ (((p1 ∧ (p1 → (p3 ∧ p4))) → True) → (((((((p2 → True) ∧ True) ∧ (p3 ∧ (p4 ∨ p3))) → p5) ∧ p3) ∧ True) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62032758689007491793226289940 : ((p2 ∧ ((p5 ∧ p3) ∧ ((p5 ∧ ((p5 → (p2 ∨ (False ∨ False))) → p2)) → ((((True ∨ True) ∧ p5) ∧ p4) ∧ ((p1 → p5) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119145869257149598304222901847 : ((p1 → (p2 → (p4 ∨ ((p1 → p5) → (p3 → (False ∧ (p4 ∧ (True ∨ (True ∨ ((p4 ∨ ((p2 ∨ p4) → p5)) ∧ False)))))))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134971197900448487371916556499 : ((((p2 ∧ (p2 ∧ (p4 ∨ True))) ∧ ((p2 ∧ p4) ∨ ((((p1 ∨ p3) ∨ p4) → (p5 → p1)) → p5))) ∧ (p4 ∧ p5)) ∨ ((p1 ∧ p4) → p1)) := by
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
theorem thm_5_vars_737220051559331648828413648342 : ((((p4 → True) ∧ ((p2 ∨ (((p2 ∧ (p1 ∨ (p5 ∧ False))) → p3) ∧ p4)) → (p4 → ((True → (p5 ∨ p5)) ∨ ((p4 ∧ True) ∧ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634600257687991723799088853694 : (((((True ∨ ((((p2 ∨ (((p1 ∧ (p1 → p5)) ∨ (p1 ∧ p5)) ∧ False)) → p4) ∨ True) ∨ (p5 → False))) ∧ ((False ∨ p4) → p1)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55216109989666528851504963375 : (((((p2 ∨ p2) ∨ False) ∨ (p4 ∨ p5)) ∨ ((((((p3 ∧ p4) ∧ (p1 → p1)) → (p2 ∨ p4)) ∨ (p3 → p3)) ∨ p1) ∨ (p4 ∧ p2))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194940154089691278129778947443 : ((((True ∨ (False ∧ p2)) → (p4 ∧ False)) → p2) ∧ ((p3 ∨ ((((p4 → (False ∧ p4)) → (p4 ∨ (p4 ∧ p1))) → False) ∧ (p2 ∨ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (False ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780843265901246470311210051139 : (((p2 ∨ (((p2 ∧ (p1 ∨ p5)) ∨ p1) → (False ∧ (True → (((True ∨ p3) ∨ (False ∧ (p4 ∨ p5))) → (p2 ∨ (True ∧ (p1 ∨ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184577197516710549690789970121 : (((True ∧ (p5 → (((p2 → p4) → False) → p3))) → (p4 ∨ p4)) ∨ (((p4 → (p5 → ((True → p1) ∧ (p3 ∨ False)))) → True) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218362046755552282759887806449 : (((p3 → p1) ∨ (p5 ∨ p4)) → (((((p1 ∨ (p1 ∧ p4)) ∨ ((True → p2) → False)) ∨ (p1 → p1)) ∨ ((p1 → p3) ∧ (p4 ∨ p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691936428624465297002931879706 : ((((p3 → ((p3 ∧ p2) ∨ (((p3 ∨ ((False ∨ p3) ∨ (True ∧ p1))) ∧ p5) ∨ False))) → ((p3 ∧ (p1 ∧ (p3 ∧ p4))) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658097635338119036979208607933 : ((((p3 ∧ (p4 ∧ (((True ∨ (p2 ∨ (p1 → (p2 → p1)))) ∧ (p1 ∨ p4)) ∧ (p5 ∨ (((p4 ∨ p5) → p2) → p5))))) ∨ (p2 → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148855974328316987956166130363 : (((p2 ∧ ((False → p5) → p2)) ∧ (p2 ∨ (((p3 → (True ∧ p1)) ∨ p3) ∨ (p4 → (False ∧ (p4 → p2)))))) ∨ (((False ∧ True) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348176626255207195727831403581 : (p3 → ((p2 ∨ p4) → (((p3 → p4) → ((((p4 ∧ p1) → True) ∧ (True ∧ True)) → ((p5 ∨ p4) ∧ ((False → p4) → False)))) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_227227663759505454493504349334 : (((False → p1) → p1) ∨ ((False → p2) ∧ ((((p2 → (True ∧ p1)) ∨ ((p2 → p3) → p3)) ∨ True) → (p5 → (((p1 ∧ True) ∨ p2) ∨ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
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
theorem thm_5_vars_116921834045065559382002394285 : (((True ∧ p5) → ((p3 ∧ ((p5 ∨ (p2 ∧ (p4 ∧ (((p3 → (p1 ∨ (p3 → True))) ∨ False) ∧ p4)))) ∨ p5)) ∨ (True ∧ p4))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257808087230297215420693962793 : ((p3 ∨ p5) → ((p2 ∧ ((((p5 ∨ ((p3 ∨ (p1 ∨ p5)) ∧ True)) ∧ False) ∨ (True ∧ (False ∨ True))) ∧ (p5 → p4))) ∨ (False → (False ∧ p1)))) := by
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
theorem thm_5_vars_209296926721872279105671483057 : ((True → (True ∧ ((p1 ∧ False) ∧ p1))) → (p5 ∧ ((((p1 ∧ p3) ∨ p5) ∧ p5) ∨ (p2 ∧ (p3 ∨ (False ∧ (((True ∧ True) → p3) ∧ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207925686529296439453373524467 : (((p1 ∨ (False → p5)) ∧ (True → p1)) → ((p5 ∧ ((((p2 ∧ p4) ∧ (True → p4)) ∧ (p2 ∧ False)) ∨ (p2 ∧ (True ∧ True)))) ∨ (False ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39313226454962138087357486069 : (((p2 ∧ ((((True → (True → ((((p3 → p3) → (True ∨ (p1 ∨ ((True → p1) ∨ False)))) → p1) ∨ False))) ∨ p4) ∧ p1) ∧ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40392772985229333054326127875 : ((((((False ∨ (True ∨ (p3 ∧ (True ∨ p4)))) ∨ (p4 ∧ (((p3 ∨ (True → (p5 ∨ False))) → p5) ∧ p5))) → (p2 ∧ p5)) ∨ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668714958644433315508070239111 : (((((((((True ∨ ((p2 → p5) ∨ p3)) ∨ (p2 → (p1 ∨ ((False → p1) ∧ p5)))) ∨ p1) → False) ∨ True) ∨ p1) ∨ (p2 ∨ (p5 ∧ p2))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_48723059332384117203575506693 : (((((p3 ∨ p4) ∧ (p4 → p3)) → (p3 ∨ (p5 → ((p5 ∨ p3) → ((p1 ∧ p2) ∨ ((False ∨ p3) → p3)))))) ∧ ((p4 → False) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251861690263758854940256720011 : ((p3 → p5) ∨ (((((True → ((((p5 → p4) ∧ False) ∨ p1) ∧ p4)) ∧ True) → p2) → p1) ∨ (((p3 → (True ∨ p4)) ∨ p3) ∧ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148602254349883341276655056182 : (((p5 ∨ ((((p5 ∧ p4) ∧ (p2 → False)) → False) → p3)) ∨ (True → ((p5 ∨ (p1 → p1)) ∧ (p1 → p1)))) ∨ (p3 ∨ (False ∨ (p4 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42867533346115613104217302510 : (((p2 → ((p4 ∧ True) → (((((p3 → True) ∨ p2) ∨ False) ∧ (p3 ∨ ((p3 → ((p5 → False) ∧ (False ∨ p1))) ∨ p2))) ∧ p3))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605962947842862650434973844706 : ((((p5 → (((((p3 ∨ (False ∧ p2)) ∨ (p1 ∨ p5)) → (p5 → (p4 ∨ p3))) ∨ p5) ∨ ((False ∧ p3) → (p2 ∧ (p3 ∨ p5))))) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219595303321827372147606707767 : ((True → (False ∨ (p4 → p3))) → ((p2 ∧ ((p2 ∨ p4) → p1)) → ((p2 ∧ (p2 ∧ ((p4 → True) → ((p2 ∧ (p3 → p5)) ∨ p2)))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670129058299945564729506009493 : ((((((p1 → p2) ∧ (p2 → (p2 ∨ p5))) ∨ (p4 → ((((True → True) ∧ ((p4 ∨ True) → p5)) → p1) ∧ p5))) ∨ ((False ∧ p1) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110769059435026153640001931879 : ((((p2 → (((p3 → (((p2 → (p1 → False)) ∧ ((p5 ∧ p4) ∧ (p3 → p1))) → (False ∨ p1))) ∨ p2) → p5)) ∧ True) ∧ p1) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118240691910917851314207517867 : ((p1 ∨ (((((p3 ∨ p2) ∧ ((p3 ∧ False) ∨ p2)) ∧ p2) ∨ (p5 ∧ ((((p2 ∨ p2) → False) ∧ p5) → p3))) ∧ (p2 → p4))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64038668580396058650319639498 : ((False ∨ (((p1 ∧ ((p3 ∨ ((p3 ∨ ((p5 ∧ ((p4 → True) ∨ p2)) → p4)) ∨ (p3 ∨ False))) ∧ p4)) ∧ p1) ∨ ((False → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753828273857632916231354916641 : (((False ∧ ((p3 → ((p5 → p4) ∧ (p1 ∨ (p1 ∨ (True → True))))) ∨ (p3 ∨ ((True → ((p3 → (p2 → False)) ∨ (p2 → p3))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135363733748739956981439144831 : (((p3 → (p1 → (((False ∨ p4) → p1) → ((True ∧ ((p1 ∨ p5) ∧ (p4 ∧ False))) ∧ p5)))) ∧ (p2 → (p4 ∨ p1))) ∨ (True ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111973700601942604168848893164 : (((((False → ((p5 ∧ p5) → False)) ∧ p4) ∨ (((p5 ∨ (p1 ∨ (p3 ∨ (p3 ∧ (p3 ∨ p3))))) ∨ p4) ∨ (p5 → True))) ∨ p2) ∨ (False ∧ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38668000223371662156598006737 : ((((((p1 → p3) ∧ (p5 ∨ p4)) ∨ p1) ∧ ((p5 → (((False → p1) → p1) ∨ (((p3 → p3) ∧ False) ∧ (p4 ∨ p3)))) ∧ p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158330849013136888866021606621 : (((False ∧ False) ∧ ((p4 ∨ (p4 → (p4 ∧ (True ∨ ((False → p2) → (p5 ∧ True)))))) → (True → False))) ∨ ((p3 ∧ (p5 ∨ p4)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709307748938030906340505107979 : (((((p5 ∧ p1) → (p3 → (p1 ∨ (p1 → p5)))) → (False ∧ ((p5 ∨ (((p4 ∨ p5) ∨ ((p5 ∧ True) ∧ (p4 ∨ p1))) ∧ False)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338128099578554899708345196226 : (p1 → (((p4 ∧ (((p5 → True) ∨ p4) ∧ p2)) → False) ∨ ((False ∨ (p1 ∨ ((True ∧ ((p5 ∧ (p2 → p3)) → True)) ∨ p3))) ∨ (p4 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84772470811585524583258720426 : ((((p2 ∧ (False ∨ p2)) ∨ (p2 → (((p1 → p3) → (p1 → p3)) → True))) ∧ ((p4 ∨ (((p5 ∧ p1) ∧ (p4 ∨ True)) ∨ True)) → p5)) → p5) := by
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
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p4 ∨ (((p5 ∧ p1) ∧ (p4 ∨ True)) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ (((p5 ∧ p1) ∧ (p4 ∨ True)) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h13



