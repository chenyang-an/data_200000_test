variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950621305830264892137390094116 : ((((p1 ∧ (p5 → True)) ∧ ((p1 → ((((False ∨ (((True → p3) ∨ True) → p1)) → ((p4 ∨ (True → p5)) ∧ False)) ∧ False) ∧ p3)) ∧ True)) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621651543024608516131155705506 : ((((False ∧ (p3 ∧ (p4 → (p2 → (((False ∧ ((((True → p3) → p4) ∨ (p4 → (True ∧ p5))) ∧ p3)) → False) → (True → False)))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47418132766735353527040176756 : (((p1 ∧ ((((True → (p3 ∧ (((p1 ∨ (p1 ∨ False)) → ((p5 ∨ p5) ∧ (p3 → p3))) → False))) ∨ p5) ∨ p2) ∨ p5)) ∨ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119345825291484799800471054254 : ((p3 → ((False ∨ p4) ∧ ((p2 ∧ (p3 ∧ (p4 → ((p2 → False) → (((False → p1) ∧ True) → ((p1 ∨ p5) → p2)))))) ∧ p5))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116057523359204993776853323736 : ((((True ∧ p5) ∧ p4) ∧ ((((((p4 ∨ p4) ∧ p2) ∨ p3) ∨ p4) → (p1 ∧ p5)) ∨ (False → ((p3 ∧ p3) ∨ (False ∧ p3))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112850413453224953413957381980 : ((((p1 ∨ (True ∨ p2)) ∧ ((((False → (p2 ∧ (True ∧ (((p3 → p3) ∧ p1) ∧ True)))) ∨ False) → (p2 ∨ p5)) → p3)) → p4) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630781687625978911207352910869 : (((((p5 → ((False ∨ (p3 ∨ (p2 ∨ (((((((p4 ∧ (p5 ∧ p1)) → p5) → True) → True) → p1) ∧ p4) → p5)))) ∨ p2)) ∨ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678634616679646948331603043591 : (((((True → p4) ∧ (((((p3 → (p2 ∨ ((p1 ∨ (p3 ∧ p5)) ∧ p5))) ∨ p5) → p5) ∧ False) ∨ False)) ∨ ((p1 ∨ (False ∧ p4)) → p1)) ∨ p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620119163443297889782329110185 : (((((False ∧ p2) ∨ (p3 ∨ ((p4 → ((p4 ∧ p2) ∨ ((False ∧ p5) ∨ p5))) → (p3 ∨ (((p5 ∨ p2) ∧ p2) → (p4 ∨ p2)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791186707905088802180949860848 : (((True → ((False ∧ ((p3 → (p5 ∨ (p4 ∧ ((True ∨ (p2 → (False ∧ p4))) ∨ (p1 → (True ∧ ((p4 → p1) ∨ True))))))) ∨ False)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148652266348040611777623369070 : ((((p4 ∧ (p2 ∨ True)) ∨ ((p3 ∧ p3) ∧ p3)) ∧ ((p5 → (p4 ∨ (p5 → p3))) → ((True ∨ p2) ∧ p5))) ∨ (((p3 ∧ p5) ∨ False) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206464676539997640259094820108 : ((p4 ∨ (p1 ∨ ((p3 ∨ p4) → p1))) ∨ ((((False ∧ p2) → p5) → (p1 ∨ p1)) ∨ (p1 ∨ (((True → (p4 ∧ p2)) ∨ True) ∧ (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214337743753125661185699618411 : (((p2 ∨ (p4 ∧ True)) → p1) ∨ (p3 ∨ ((p4 ∧ p4) ∨ ((False ∨ (p2 ∨ ((p4 → p2) ∨ ((p3 ∧ (False ∨ p5)) → p3)))) ∨ (p4 ∧ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747536990799627945127726643975 : ((((True → p2) → (((p4 → p3) ∨ p1) ∨ ((((p5 ∧ p5) → p2) ∨ ((p3 → (p4 → p4)) → ((False ∧ False) → (p2 ∨ False)))) → p2))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118561849643854612578580943400 : ((p4 ∨ ((((p4 → (((p2 ∨ ((p1 ∧ True) ∨ p5)) ∨ (p2 ∧ True)) ∧ True)) → (((p1 ∨ p1) ∨ True) ∧ p2)) ∨ p3) ∧ True)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42697556481957702392760605139 : (((p5 ∨ ((((False ∧ (((p4 → p1) ∧ p3) ∨ p3)) ∨ p2) → (p4 ∧ (p3 ∨ (p4 → (p3 ∨ p1))))) ∨ ((p4 ∧ p5) ∧ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353352353125413616322506430956 : (p4 → (False ∨ (((p4 ∧ p2) ∧ ((False ∨ (((p2 ∨ (True ∧ ((p5 → p2) ∨ (True ∧ False)))) ∧ p3) ∧ p1)) ∨ ((True → False) ∧ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342324383173004299947187738038 : (p2 → ((((True ∧ False) ∨ (((p2 ∨ p4) ∨ p3) → p1)) ∨ ((p3 ∨ ((p2 → p5) ∨ p2)) ∧ p3)) → (p5 → ((False ∧ (p3 ∨ p2)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
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
theorem thm_5_vars_742927432359080779282106612446 : ((((p3 → p4) ∨ ((((False → p5) ∨ True) → ((p1 ∧ p3) ∨ (p1 ∧ p4))) → (p1 ∨ (p4 → (True ∧ (p5 ∨ (p5 → (p3 ∨ False)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165791318577440797237829921207 : (((p3 → ((p5 → True) ∨ p3)) → (False ∨ ((p1 ∨ p1) ∧ (p1 → (p4 ∨ (p5 → p3)))))) ∨ ((True ∨ p2) → (((p2 → p1) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134825991875922647418823688603 : (((p1 ∨ ((p1 ∨ (((p3 ∨ ((True ∨ p2) → (False ∧ p1))) ∧ (False → (p3 ∨ p4))) ∨ p5)) ∨ (p5 ∨ False))) → False) ∨ ((False ∨ False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679837501403176277946830626616 : (((((p2 ∨ (((((((p3 ∧ p2) ∨ p5) ∨ False) ∨ True) ∧ p4) → ((p4 ∧ p1) → p5)) → False)) ∨ p5) → ((True ∨ p5) ∧ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258237965291690135397330244222 : ((p4 ∨ p5) → (((((p2 ∨ (p3 ∧ False)) ∧ p3) ∨ True) ∨ ((False ∧ (p4 ∧ True)) ∨ p2)) ∧ (((p2 ∧ (p3 ∧ p5)) ∨ False) ∨ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_166456552231351654608661726236 : ((p2 ∨ (((p3 ∧ p5) ∧ p2) ∧ (((p1 → (((p4 ∧ p4) → False) ∧ p1)) → True) → p5))) ∨ ((p3 ∨ (True ∨ p1)) ∨ (True → (p3 ∨ p2)))) := by
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
theorem thm_5_vars_963394306645657400613397960270 : ((((p2 → p4) ∧ ((((((False ∧ (p1 → p5)) ∨ p2) ∧ p3) ∨ True) → False) ∧ (((((p1 ∧ p2) ∨ p1) ∨ p3) → (p5 → p4)) → p4))) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((((False ∧ (p1 → p5)) ∨ p2) ∧ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133901728717765475208922858579 : (((p1 ∨ ((True → (True ∧ (p3 ∧ p4))) → (p2 ∧ (p5 ∨ ((True ∨ (p2 ∨ (p1 ∧ False))) ∧ (p1 ∧ p2)))))) ∧ p2) ∨ ((True → False) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162049475443404903515576916634 : ((p5 → (((p4 ∨ (((p1 ∧ p1) ∨ p1) → (p2 → (False ∧ ((p4 → False) ∨ p1))))) → p5) ∧ p3)) → (((p3 ∨ p5) → p3) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158804871531569810836759238516 : ((p5 ∧ (True ∧ (((True ∧ p5) → p4) → ((((p2 ∨ p5) ∧ p5) ∧ False) → (p1 ∨ (p5 ∨ p5)))))) ∨ ((p5 ∨ p5) → ((p4 → p2) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66112185093748676003814479416 : ((p5 ∨ (((p1 → p1) ∨ (((True ∨ p3) ∨ ((p5 → ((p2 → p4) ∨ (p2 ∨ p5))) ∧ (True → (p3 → False)))) ∧ (p2 ∧ p4))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264903007874840476377636750646 : (True ∧ ((True ∧ p1) → ((p4 ∧ (((((p4 ∨ p1) ∨ True) ∨ p3) ∧ ((((p5 → p3) ∧ False) ∨ True) ∧ True)) ∧ (p3 ∨ (p5 ∧ False)))) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_322422253449663251483723224329 : (p5 ∨ ((((p4 ∨ ((p3 ∨ p2) ∧ p3)) ∧ (p4 ∧ True)) ∨ (p2 → (((p1 ∨ p4) ∨ (p3 ∨ p3)) → (p2 ∨ ((p5 ∧ False) ∧ p4))))) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257695904434198943930927145314 : ((p3 ∨ p3) → ((p2 ∧ (False ∧ (p1 ∨ (False → (p2 ∧ False))))) ∨ ((((False ∧ (p1 ∧ False)) ∨ True) ∨ (p3 ∧ (p4 ∧ (False ∨ False)))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    exact h2
  case inr h3 =>
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
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134268650528093947514140421807 : ((((False ∧ p4) ∧ (p3 ∨ (((p3 → ((p5 → False) ∧ (True → (p4 ∧ (p2 ∧ p4))))) → (p5 → p4)) ∧ p2))) ∨ False) ∨ ((p2 ∧ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615128610274069620987227186399 : (((((((((True → p2) → (True → p1)) ∨ ((p4 ∧ p4) → (p4 → p1))) ∨ False) → p2) ∧ ((((p3 → True) ∧ p4) → p3) ∧ p2)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174245249851021567953542839609 : (((p3 ∨ (p5 ∨ ((p4 → p3) ∨ (((p3 → p1) → p5) → True)))) → (True → p3)) → (p3 ∨ ((False ∨ (p3 ∨ ((p3 → p2) ∨ p4))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p5 ∨ ((p4 → p3) ∨ (((p3 → p1) → p5) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3235839568261174620653967059 : ((p3 ∨ False) ∨ (((((p1 ∧ ((p2 → (False ∧ (p3 → True))) ∧ False)) ∧ False) ∧ (p1 ∧ (((p5 ∨ False) → p3) ∨ p5))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46535692136816509090639835996 : ((((p2 ∨ p2) ∨ (True → ((p3 ∨ ((p3 ∨ ((p2 ∨ (p2 ∨ p3)) ∧ (p3 ∨ (True ∧ p3)))) → (p3 ∧ p2))) ∨ p5))) ∧ (p5 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37748247924833250126004576488 : ((((((False → (p2 → p4)) ∨ (p4 ∧ p5)) ∨ ((p3 ∨ ((((p4 ∨ True) → p3) → p3) → p1)) → ((p3 → p3) ∧ p2))) → p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722228847007068038987435522702 : ((((p5 → (p5 ∧ (True ∨ p4))) → (((((((p3 ∨ False) ∨ (p2 ∨ p5)) ∨ p5) ∨ (p2 ∧ p3)) ∨ p1) → (p2 ∨ (p4 ∧ False))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112226741461910708821893057828 : (((p1 ∨ (p5 ∨ (p5 ∧ (((p5 ∨ True) ∨ (p5 ∧ ((p2 → (p3 → (True → p5))) ∨ (p5 ∨ True)))) → (p1 ∨ p5))))) ∨ True) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45362658974685296125740150488 : (((p4 ∧ ((((((p1 → False) → p5) ∧ p1) ∧ (p5 → p1)) ∨ p4) ∧ (((((p4 ∧ p4) → p5) → False) ∨ p1) → (p3 ∨ p2)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165707744836722959018341987668 : ((((p4 ∨ (False ∨ p4)) ∨ p3) ∧ ((False ∨ ((((True ∨ p5) → p1) ∧ p2) ∧ False)) ∧ True)) ∨ (p3 ∨ (True ∨ ((p1 ∧ (p5 → p2)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679163067658834970880628369046 : ((((p4 ∨ (((True ∧ p1) → (True → ((((p2 ∨ True) ∧ (p4 → p5)) ∧ False) ∧ p1))) ∧ (False ∧ p4))) ∨ (False → (True ∨ (p5 ∧ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259022023211104535425808751840 : ((True → p4) → (((((p2 → (((((p3 ∧ p1) → p3) ∨ (False → p3)) → (p4 ∧ p3)) → p4)) ∨ p5) → p5) ∧ p1) ∨ ((p5 ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148765905874612181451775419626 : ((((p3 ∨ ((False ∧ p2) → True)) ∧ p5) ∨ (((False ∧ (False ∧ True)) → True) ∧ (p5 ∧ (True → (p5 ∧ False))))) ∨ ((False → p4) ∧ (p4 → True))) := by
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
theorem thm_5_vars_151212422652967944984485590098 : ((((p1 ∨ ((False ∧ False) ∧ p4)) ∨ (((p3 ∨ p3) → p2) ∨ (p4 ∨ (p5 → ((True ∨ p3) → p2))))) → False) → (((p3 ∨ p2) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ ((False ∧ False) ∧ p4)) ∨ (((p3 ∨ p3) → p2) ∨ (p4 ∨ (p5 → ((True ∨ p3) → p2))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h3
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206026125839080933149641526068 : ((p2 ∧ ((p3 → (p1 → False)) → p2)) ∨ (((True → ((p3 ∧ (p1 ∨ p4)) ∨ ((p4 ∧ True) ∧ (p5 ∨ (p5 ∧ False))))) ∨ True) ∧ (p2 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60610904754209908716235456970 : ((True ∧ (((p1 ∧ ((p4 ∧ (p1 ∧ ((((((True → p4) ∨ True) ∨ p4) → p5) ∧ (True ∨ p2)) ∧ True))) ∧ p2)) ∨ False) ∨ (p5 → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141665472942788253791476702790 : (((p1 ∧ p4) ∧ ((False ∨ (p5 ∨ p4)) → (p3 ∧ ((True → ((p1 ∨ False) ∧ (True ∧ (p1 ∧ (False ∨ False))))) ∨ False)))) → ((p1 ∨ p5) ∧ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : (False ∨ (p5 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683847286407060891470501812092 : ((((((p5 ∧ p4) ∨ (((p2 → ((p3 ∨ p1) ∧ (p5 → (True → p5)))) ∧ p2) ∧ p5)) ∨ p4) ∨ ((p2 ∨ ((True ∧ False) → p1)) ∨ p1)) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159244120884999786644828922459 : ((p3 → (((p2 ∧ (p4 ∧ p4)) ∨ ((p1 → p3) → p3)) ∧ ((False ∧ p5) ∨ ((p1 ∧ False) ∧ p3)))) ∨ ((p2 ∨ True) → ((p2 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607137122076254638936581857448 : ((((((((((p1 ∧ False) → p2) → p1) ∨ p1) → p5) → (p5 ∨ ((((p1 ∨ p5) ∧ (True → (p4 ∨ p5))) ∨ True) ∨ p5))) ∧ True) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193558436020030708819489459053 : (((True ∨ True) → (p2 ∧ (p3 ∧ (True ∧ (p5 ∧ False))))) → ((p3 ∧ ((p1 → p2) ∧ ((((False ∨ (True ∨ p1)) → False) ∧ p2) ∨ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184476167264296713277456086316 : (((((False → p1) ∧ ((p1 ∨ p1) → False)) ∨ False) ∨ (p4 ∧ p4)) ∨ (p3 → ((p2 ∨ p1) → (p3 ∨ ((p1 ∧ (p3 ∧ p2)) ∨ (p3 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124580829085216155749672783572 : (((((p5 → p4) → p2) ∧ (p5 → p2)) ∨ (p2 ∨ ((True ∧ (((p4 ∨ p2) → (p1 ∧ True)) ∧ ((p3 → True) → True))) ∧ p2))) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336382696797949575072314842710 : (p1 → ((False ∧ (p5 ∧ (p5 ∧ (True ∧ (p5 ∧ ((((((p2 ∨ p3) ∨ p2) → p2) ∧ (p1 ∧ p2)) ∧ (p3 ∧ (p2 ∨ p4))) ∨ p2)))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_521754335477518528672015939 : (((p4 ∨ (p4 ∨ ((p3 → ((False ∨ (False ∧ ((p2 ∨ (p4 ∧ p1)) ∧ True))) ∧ p5)) ∧ (p4 ∨ ((p1 ∨ False) → p2))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326986793216969105737598451237 : (True → ((((False ∧ (False → p4)) ∨ ((True ∧ (p1 ∧ p5)) ∨ (True ∨ (((p3 ∧ False) ∧ (False → p4)) → p4)))) → ((p5 → p2) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809510993618136184970532876029 : (((p5 → ((((p1 ∧ ((True ∨ ((p4 ∧ True) ∨ p3)) → p4)) ∧ (p1 → (p1 ∧ False))) ∧ (True ∧ ((p4 ∨ p2) ∧ (True ∧ p1)))) → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h12.left
    let h21 := h12.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h22 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h23 := h6 h22
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66257086176944863878785644173 : ((p5 ∨ ((p4 → (False ∧ (False ∨ True))) ∨ (((p2 ∨ ((p5 → p3) → (p5 ∨ ((p5 → True) → p2)))) → (p4 ∨ (p5 ∨ p1))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258354135351387896706425557789 : ((p5 ∨ False) → (((p1 ∨ (p1 → (False ∧ ((((p4 → (p1 ∧ p5)) ∧ (True → p2)) → (p4 ∧ p3)) ∧ p1)))) ∨ p5) ∨ ((p5 ∨ p5) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57433986079948927194796922760 : (((p3 ∨ (p5 ∨ False)) ∨ (((p4 ∨ (p3 ∧ (False → (((p1 ∨ True) ∨ False) ∧ p3)))) ∨ (((True ∨ p5) ∨ (p3 ∧ True)) ∧ p1)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350200804656539145950779133228 : (p4 → (((p2 ∨ (p2 ∨ p1)) ∨ (((p2 ∧ p4) ∧ (True ∧ p3)) → (p5 → (((False ∨ (p5 ∨ (p1 → p4))) ∧ p1) ∨ (p5 ∧ p4))))) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787181063088188179990905029837 : (((p4 ∨ ((p5 → p4) → (p2 → ((((((False ∧ ((p5 → True) → p1)) ∧ p3) ∨ p1) ∨ p2) ∨ ((p2 ∨ (True ∧ False)) → p1)) ∨ p3)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263375500976477547738382825199 : (True ∧ ((((True → ((((((p2 ∨ p2) → (True ∨ p2)) ∧ p5) ∧ p1) → (p2 ∧ p3)) ∨ p2)) ∧ (True ∨ p3)) ∨ True) ∨ ((p5 ∨ p3) ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681050685690526285548945076616 : (((((True → p5) → ((p5 ∧ (((p4 ∧ (p4 ∨ True)) → p1) ∨ ((p2 → False) ∨ p2))) ∧ (p2 ∧ p5))) → ((p5 ∧ False) ∨ (p4 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347099258190547841777608695113 : (p3 → (((False ∧ (((False ∧ p3) ∨ False) ∧ ((p4 ∨ p2) ∧ (p3 → p3)))) ∨ False) ∨ ((p5 ∧ ((False ∧ p3) ∧ ((p1 ∧ p5) → p3))) → p3))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65203309159050801220796745305 : ((p3 ∨ (((((((True → p4) → ((((p1 ∧ p2) ∧ p5) ∧ True) ∧ (p4 → p1))) ∨ ((p2 ∨ p5) ∧ p3)) → p3) ∨ p2) → p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137485436022018273840282994803 : ((p5 ∧ ((((True → False) ∧ (((((p4 ∨ True) ∧ p3) ∨ False) ∧ (p1 ∧ p1)) → ((p5 ∧ p4) → p4))) → p5) ∨ p4)) ∨ ((p5 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47164243419013059565567052899 : (((((p1 ∨ ((True → p4) ∨ ((p3 ∨ p2) → p2))) ∨ (False → (p4 ∧ p1))) ∧ (((p2 → True) → p3) ∨ (p2 ∧ p5))) ∨ (p5 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133577034838770092605202999705 : ((((((p4 ∧ (True ∧ (p2 ∨ True))) ∨ p5) → ((p5 ∨ False) → (((False ∨ False) ∨ p2) ∧ (p5 ∧ p2)))) ∨ True) ∧ True) ∨ ((p3 → False) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321616381646488486495473345883 : (p4 ∨ (p3 → ((((((p2 ∧ p1) ∨ p2) ∧ p3) → ((p5 → ((False → p4) ∨ p5)) ∧ p3)) → False) → (p2 ∨ ((p1 ∨ (p4 ∧ False)) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p2 ∧ p1) ∨ p2) ∧ p3) → ((p5 → ((False → p4) ∨ p5)) ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h18 := h2 h3
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680841972416252194464423483291 : (((((p5 → (True ∨ p2)) ∨ (((p1 ∧ (p3 ∧ (True ∧ p5))) ∨ (p5 ∨ ((False ∧ p5) ∨ p4))) ∧ p1)) → ((p3 → (True ∧ p2)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178746932068007240484663745347 : (((p3 → ((p4 ∧ p2) ∨ p3)) → ((p1 ∧ p3) ∨ (p1 → (p2 ∧ p1)))) ∨ ((((p4 ∨ p3) ∨ p1) ∨ (False → (False ∧ (p4 ∨ p5)))) ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111565898753619311866465035409 : (((((p2 ∧ (True → (False → p1))) ∧ (((p5 ∨ ((p1 → (True ∧ p1)) ∧ p1)) ∧ ((p4 ∧ p3) ∧ p2)) ∨ p5)) ∧ p2) ∨ True) ∨ (False ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336553455568061648309051089379 : (p1 → (((((p2 ∨ True) ∧ p5) ∧ ((((((False ∧ p2) ∧ p4) ∨ p5) ∧ ((p5 ∨ (p3 → p1)) ∨ (p1 ∨ False))) → False) ∧ p2)) ∨ False) → p3)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : ((((False ∧ p2) ∧ p4) ∨ p5) ∧ ((p5 ∨ (p3 → p1)) ∨ (p1 ∨ False))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : ((((False ∧ p2) ∧ p4) ∨ p5) ∧ ((p5 ∨ (p3 → p1)) ∨ (p1 ∨ False))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164552042151968784304791634474 : ((((p1 ∨ ((p4 ∧ p3) ∨ (False ∨ False))) ∧ (((p2 → p5) ∨ (p1 ∨ True)) ∧ p5)) ∧ p3) ∨ (((p1 ∨ p5) ∧ (p2 ∧ (False → p2))) → p2)) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49501096354955584400960490900 : ((((p5 ∧ ((False ∧ p5) → ((((p4 ∨ True) → p2) ∧ (p2 ∨ ((False ∧ p4) ∨ (p3 → p3)))) → False))) → p2) → (p5 ∨ (p5 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301567949007150336587594271582 : (False ∨ ((p3 ∨ (p3 ∧ p3)) ∨ ((((((p3 ∧ p5) ∧ p4) ∧ ((p5 → p1) ∧ p1)) ∧ p2) → False) ∨ (((p2 ∧ p2) → (p5 → p2)) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37396110933270114143051423889 : (((((p5 ∨ (p5 ∧ ((p4 ∧ (((p2 ∨ (p2 ∨ p2)) ∨ (False → ((p3 ∧ p3) ∧ (p4 → p1)))) ∨ p1)) ∧ p1))) → p3) ∨ p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345368593153826512319133299198 : (p3 → (((((((p2 ∨ True) ∨ (p1 → (False → p5))) → ((p1 ∧ True) ∨ False)) → False) ∨ (((p4 ∨ True) → True) → (p5 ∨ False))) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178149868055175060038574236958 : ((((p5 ∧ (p2 ∨ p4)) ∨ ((p2 ∨ True) ∨ (p1 ∧ (True ∨ p2)))) → p4) ∨ ((p4 ∨ (((((True → p3) → p4) ∧ p3) → p1) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181340385229108333129338737357 : ((False ∨ (((p1 ∨ ((p1 ∧ ((True ∨ False) ∨ p3)) → p1)) ∨ p4) ∧ p3)) → (p1 ∨ ((p4 ∨ (p5 ∧ (False ∧ True))) ∨ (p3 ∨ (False → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178607885533957649596280372569 : (((False ∨ ((p1 → (p3 ∧ p1)) → p4)) ∨ ((True ∨ False) → (p3 → p1))) ∨ (((p5 → False) ∨ p2) → ((((p3 ∧ p4) ∧ True) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138175263230259878355926197201 : ((p1 → (((True ∨ (False ∧ False)) ∧ (False → False)) → ((p3 → ((p3 → p5) ∨ (p5 ∧ ((False ∧ p5) ∨ p2)))) ∨ True))) ∨ ((False ∧ False) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64930947513017503556895595794 : ((p2 ∨ ((p2 ∨ (((((p4 ∧ (p1 ∧ p4)) ∨ (p1 ∧ p5)) ∧ p1) → p2) → p5)) ∨ ((p1 → (p4 → ((p1 → True) ∨ True))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116798321607865942920130977688 : (((p2 ∨ p3) ∨ (p4 ∨ ((p1 ∧ (((p4 ∨ (p4 → (False ∨ p5))) ∧ ((p4 → p3) ∨ p5)) → (True → p4))) ∨ (p2 ∨ True)))) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_340208425307972490032009433711 : (p1 → (p5 → ((((((True ∧ ((p2 ∨ ((p4 ∧ p4) ∨ ((p1 → ((p2 ∧ True) → p4)) ∨ p4))) ∧ p1)) → p5) ∧ p3) → p4) ∧ p4) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166200553164935408112132903939 : ((p1 ∧ ((True ∧ p2) → ((p1 ∧ ((p3 → p4) ∧ (((p2 → p2) → p2) → True))) → p3))) ∨ ((p4 ∨ ((p3 → p5) ∧ (False ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301244454753340992716764725266 : (False ∨ (((p5 ∨ (False ∨ (p2 ∧ p1))) ∨ p1) ∨ (((p3 ∧ p3) → p3) ∧ (p2 → ((p4 ∧ (p1 ∧ p4)) → (((p5 ∧ p4) → p1) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h5.left
  let h10 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58323272200927183280008284799 : (((False ∨ False) ∧ ((((False → (p5 ∨ ((p3 ∧ p1) → True))) → ((p2 ∨ p3) → p2)) ∧ p3) → (((p3 ∨ False) ∧ p2) ∨ (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167329893266156650851539745660 : ((((p5 → (False → ((((p3 → p1) → (p4 ∨ True)) → p3) ∨ True))) ∨ (p2 → p5)) → False) → (((p5 ∧ ((p4 → p4) → p1)) ∧ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (False → ((((p3 → p1) → (p4 ∨ True)) → p3) ∨ True))) ∨ (p2 → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37322962174290721642637930384 : ((((((((p4 ∨ True) → False) → (True ∧ (((p1 ∧ True) ∧ True) → ((p4 ∧ (p1 ∧ p4)) ∨ (True ∨ False))))) ∧ p1) ∧ p2) ∨ p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156863510080783755918935241306 : ((((((p4 → p3) ∨ ((p4 ∨ (p5 → (p5 ∨ p4))) → p4)) ∨ ((p2 → False) ∨ False)) ∧ p5) ∨ p1) ∨ ((p1 ∨ True) ∨ ((True ∧ p2) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135581184862294530078528327596 : ((((((p5 → (p4 ∨ (p3 ∧ (False → ((p4 ∨ p2) ∧ p5))))) ∧ p2) → False) → p5) ∨ (((p5 ∨ p4) ∨ p4) ∨ p2)) ∨ (p2 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41903901255248340495019119341 : (((((p1 ∧ p2) ∨ p1) → (((p4 ∨ (False ∧ (p5 → (((p3 ∨ p2) → False) → (p3 → True))))) ∧ (True → (p4 ∧ True))) ∧ p5)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219811504405366738104237674512 : ((p2 → (p5 → (p4 ∧ p1))) → (((((p3 ∧ (((True ∧ (p4 ∧ p1)) → p5) ∨ ((p2 ∧ p4) ∨ (False ∧ True)))) ∧ p3) ∨ True) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51930964217593939989073234316 : (((((((p5 ∨ (True → True)) ∨ (p4 ∨ p5)) ∨ p5) → p5) → (False ∨ (False ∧ p4))) ∨ (False → ((p3 → (p5 ∨ (p3 → True))) → True))) ∨ False) := by
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
theorem thm_5_vars_55653725967024074080960962011 : ((((False ∧ (p2 ∨ p1)) ∧ p3) ∧ (True ∧ (((p1 ∧ (p4 ∧ p5)) → ((p4 ∨ True) → (p4 ∨ (((p2 ∧ p5) → True) → p5)))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63942235330541355382804323541 : ((False ∨ ((((p1 ∨ p2) → ((p4 → p2) ∧ p1)) → ((p5 ∧ p1) → ((p3 ∧ ((p1 → p4) ∨ ((p4 ∧ p1) ∧ True))) → p4))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



