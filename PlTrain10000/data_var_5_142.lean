variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804994764197714272241888265451 : (((p3 → ((p1 ∨ p4) → (((p4 ∨ p5) ∨ ((p5 ∨ p1) → (((p4 ∧ ((p5 ∧ (p5 ∧ p3)) → (p1 ∧ p1))) ∧ p4) ∧ True))) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190152169198952371512607179675 : ((((p1 ∨ p2) → (((True ∨ p4) ∨ p4) ∨ p4)) ∧ p1) ∨ (((((((p3 ∧ p5) → p2) → (False ∨ p3)) ∨ p3) ∨ p2) ∨ (False → False)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117858638225387030564350818515 : ((p5 ∧ (((p4 ∨ (p3 ∨ p1)) ∨ ((p2 ∧ p5) ∨ ((((((p4 → p2) ∧ True) ∨ p3) → p5) ∧ (p5 → p3)) ∧ p5))) ∧ p1)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158021311598247439063994806705 : ((((p1 ∨ p4) ∧ (p4 ∧ (True ∧ False))) ∧ (((True ∨ p1) → ((p3 ∧ p4) ∧ (False ∧ True))) ∧ False)) ∨ ((p2 ∧ False) → (p5 ∧ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197751608391225917749112743151 : (((p1 ∧ (p5 ∧ True)) ∧ (p1 ∧ (p3 ∨ False))) ∨ (((p3 → False) → (p5 ∨ p5)) → ((True ∨ ((True ∨ False) → p5)) ∨ (p1 ∧ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310781803566713229094639308350 : (p2 ∨ (((True → False) ∨ p3) ∨ ((p2 ∧ ((((((False → True) ∨ False) ∨ True) ∧ p2) ∧ (p4 → p5)) → (p1 ∧ p3))) ∨ (False → (p4 ∨ False))))) := by
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
theorem thm_5_vars_53602504040941152588773516888 : (((((((False ∧ p2) → p4) ∨ p2) → False) ∧ (p4 → False)) ∧ (((False ∨ ((False → (True → (p4 ∧ (p3 ∧ p1)))) ∨ p2)) ∨ p3) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307963989487694084304314419452 : (p2 ∨ ((((p5 ∨ (p2 ∧ (p3 ∧ p2))) ∧ (((((p4 ∧ p4) → True) ∨ p5) ∨ (p3 ∧ (((p4 ∧ False) ∧ p3) ∧ True))) ∨ p3)) ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624972315871400329298513012476 : ((((p5 ∨ (False ∨ (p5 ∨ ((p5 ∧ (p2 ∧ (p1 → True))) ∧ (p4 ∨ (p4 → ((p1 → (((p5 ∧ p4) ∨ False) → False)) ∧ p2))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186350055656450004642953644695 : ((((p3 ∨ (p2 ∧ p2)) ∨ (((False ∧ p1) ∨ False) → p5)) → False) → ((p2 → ((p4 ∧ ((True ∧ True) ∧ p1)) ∧ True)) → (True → (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ (p2 ∧ p2)) ∨ (((False ∧ p1) ∨ False) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137088087511779036097676027578 : ((True ∧ ((((False ∨ False) ∨ (((p5 ∨ p1) ∨ p1) ∨ (False → (p5 ∨ ((True → (p5 → p5)) ∨ p2))))) ∨ p1) ∨ p5)) ∨ (p4 ∨ (p2 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63908731132405316124985524885 : ((False ∨ (((p3 ∨ p3) → (p5 ∧ ((((p4 ∨ False) ∨ (((p2 ∧ False) → p2) ∧ p4)) → (((False ∧ True) → p3) → p5)) → False))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165890959256268582440662088724 : ((((True → False) → False) → (p2 ∨ (((p4 → p3) ∨ (p1 → p5)) → ((p2 ∨ p2) ∧ p4)))) ∨ (False ∨ (p5 ∨ (((True ∧ False) ∧ p2) → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320307834282353949288264700565 : (p4 ∨ ((False ∨ p2) ∨ (p2 ∨ ((((p4 ∧ p1) ∨ True) ∨ ((True ∧ p1) ∧ p4)) ∨ (p4 → ((p4 ∧ p4) → (((p3 ∧ p1) → p1) ∧ p4))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25128169670228983411649035566 : (((p1 → (p5 ∨ p5)) ∨ ((((((False ∧ p4) → (True ∧ False)) → False) ∧ p4) ∧ p5) ∨ ((p4 ∧ ((p3 ∧ p5) ∧ (p1 → True))) → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659680568422100829179655795758 : ((((((p5 ∧ (False ∧ p1)) ∨ (((((((p2 → (False → p4)) ∧ p2) ∨ p5) ∧ (False → p1)) ∨ False) → p2) ∨ False)) ∧ True) → (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322456775673739713554181821006 : (p5 ∨ (((p5 ∨ (False → p5)) ∧ ((((p5 → p4) ∨ p3) ∨ ((((p5 → p1) → (((p4 ∧ False) → p2) → p4)) ∨ p5) ∨ False)) ∨ True)) ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231733788794528169368867762240 : (((p2 ∧ p4) → p4) → (((p4 ∧ p4) → (p1 ∧ ((((((p1 → p1) ∨ True) ∧ (p3 ∨ p5)) → (p2 ∨ p1)) ∨ False) ∧ (p3 ∧ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48923483911611261551728398059 : (((((False ∨ (True ∨ ((((((p5 → True) ∧ True) ∧ (True → p1)) → p4) → (p5 ∧ False)) → p3))) ∨ p5) ∧ p2) ∨ (False ∧ (p4 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871186465597080418109178516823 : ((((p1 ∨ ((p3 ∨ p1) ∨ (((((False ∨ p1) → (p4 ∨ (True ∨ (p2 → (p1 → (p1 ∧ True)))))) → (p3 ∧ p4)) ∨ False) → p4))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p3 ∨ p1) ∨ (((((False ∨ p1) → (p4 ∨ (True ∨ (p2 → (p1 → (p1 ∧ True)))))) → (p3 ∧ p4)) ∨ False) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : ((False ∨ p1) → (p4 ∨ (True ∨ (p2 → (p1 → (p1 ∧ True)))))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h5
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766227403562019767659730363561 : (((p4 ∧ ((False ∨ False) ∨ (p2 ∨ (True → (((((True ∧ True) → (p3 ∨ False)) ∧ (p5 ∨ p3)) ∧ p4) ∨ (False ∧ (p4 ∨ (p4 ∧ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40789584313546586582362730711 : ((((p4 ∧ (((False ∧ ((False ∨ (((p1 ∨ p2) ∧ p1) ∧ (True → (p1 → ((True → True) ∨ p3))))) ∨ p5)) → False) ∧ True)) → p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49145838238786585680987071507 : (((((p1 → p2) ∨ ((p1 ∨ (True ∨ (True ∨ p3))) ∨ p4)) → (((p5 ∧ p1) → p5) ∧ ((p2 ∧ p1) → False))) ∨ (p1 → (p1 ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180496073367777827696150164099 : ((((p2 ∨ (p1 → p2)) ∨ ((True → True) ∨ p2)) ∧ ((p3 → False) → p2)) → ((((p5 → p3) → (True ∧ ((True ∧ p4) ∧ p1))) ∧ p4) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60160538832052949914163050364 : (((p4 ∨ p5) → ((((p4 → ((p4 ∧ ((p3 ∧ (p3 ∨ True)) → ((False ∧ (False ∨ p3)) ∧ p2))) → p2)) → (p4 → p1)) ∧ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248755646539335822461401938853 : ((p3 ∨ p3) ∨ (((p3 ∨ (p1 ∨ p2)) → ((True ∧ ((p5 ∧ (True ∨ True)) → (((True → True) ∨ (False ∨ False)) ∧ p1))) ∨ False)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147435383104895225618618318433 : ((((p1 ∧ False) ∧ (((((p2 ∨ (False → (p1 ∧ (False → p2)))) ∧ p1) → p5) → (p4 ∧ p1)) ∧ p3)) ∨ p3) ∨ ((p1 ∨ p1) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135714584285355078550422338540 : (((p1 ∨ (((p1 ∨ ((p1 ∨ p4) → ((p1 ∨ p1) ∨ p2))) ∨ p4) ∧ p4)) ∧ (p3 ∨ ((p3 ∧ p3) → (True → p5)))) ∨ ((p1 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629900166266903212783932202996 : ((((((((p5 ∨ p5) → p1) ∨ ((p2 → False) → p1)) → (p3 → ((p5 ∧ (False → ((p2 ∧ True) ∨ (p5 ∧ p2)))) → p3))) ∨ p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60276191655146105066035225611 : (((False → p4) → (p1 ∧ (p4 ∧ (p1 ∨ ((((p3 ∨ p4) ∨ (p4 ∧ ((True ∨ p1) → (p3 → (False → True))))) ∧ p2) ∧ (p2 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42748487603700297671499235762 : (((True → ((p5 ∧ p3) ∨ ((p5 → ((p5 ∧ (p1 ∨ (((False → (p4 ∨ (p2 ∧ p1))) ∧ (p4 → False)) ∧ p4))) ∨ True)) ∧ p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162390885804578751685398873952 : (((((p5 ∨ p3) ∨ ((p5 ∨ p2) ∧ (False ∧ ((p5 ∧ p3) ∨ False)))) ∨ (p1 ∧ True)) ∨ True) ∧ (((p2 ∨ (True ∨ p5)) ∨ (p5 ∨ p1)) → True)) := by
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
theorem thm_5_vars_149852122332518587279961905904 : ((p1 ∨ (p2 ∨ (p1 ∧ ((((p5 ∨ ((True ∨ False) ∨ p3)) ∨ (p3 → ((p3 ∨ p2) ∧ p2))) ∧ p1) ∧ p2)))) ∨ (True ∧ (p1 ∨ (False → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354966990348041459844021093523 : (p5 → ((p3 → (((((p3 → False) ∧ (p1 → ((True ∧ p5) → (p2 ∧ (p2 ∧ True))))) ∧ (((True → p3) ∨ p5) ∧ p4)) ∧ p5) → p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h17 := h8 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56598246576549737384016133477 : (((p3 → (False → (p4 ∨ p1))) → (True ∧ ((((p5 ∨ (((True ∨ p3) ∨ p3) → p4)) ∨ (p3 ∧ p2)) ∧ p3) ∧ (p5 ∧ (p3 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787401769956922871791051124953 : (((p4 ∨ (p4 ∧ ((False ∨ (p1 ∨ (p3 ∨ p5))) → (((p1 ∧ p2) ∨ p3) ∨ (p1 → ((p1 → ((p2 ∨ p2) ∧ p1)) ∧ (p2 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_400043472797520366619695440137 : ((((p4 → ((p4 ∧ True) ∧ (p3 ∨ ((p3 ∨ (p3 ∧ p1)) ∨ (p3 ∨ ((p3 ∨ (((True ∨ p3) ∨ True) → (p4 → False))) → True)))))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197751367250675389820327411142 : (((p1 ∧ (p2 ∧ False)) ∧ (p5 ∧ (False ∧ True))) ∨ (p3 ∨ (((p1 ∨ p3) ∧ (((p3 ∧ p4) ∧ (True ∨ p2)) → p1)) ∨ (False ∨ (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_258815856839213053650165618842 : ((True → False) → (p4 → ((False ∧ ((((((p2 ∧ (p1 ∨ p4)) ∧ p5) ∧ (((p4 ∧ p5) ∧ p3) ∧ p2)) → False) → (p1 ∧ p1)) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328140764074329101440988157857 : (True → ((p2 ∧ (False ∧ (p2 ∧ ((True ∧ ((p1 ∧ (p5 ∨ p2)) → p3)) ∨ (True → ((p2 ∨ p1) → (p5 ∧ p2))))))) ∨ (True ∨ (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183823097592917871006112631909 : (((((True → (p4 → True)) ∧ (False → (p1 → p4))) → False) ∧ True) ∨ (True ∨ (((False ∨ p5) ∧ ((False ∧ (p5 ∨ p1)) ∧ (p3 ∨ p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116574407958865324720726723571 : (((p3 ∨ p1) ∧ ((p2 ∧ p4) ∨ (((p5 → (True ∧ (p2 ∧ p2))) ∨ p4) → (((p1 ∧ (p3 → (p2 ∧ p3))) ∨ False) ∨ p2)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138219701567714779731654820427 : ((p2 → (((((((p1 → True) ∧ p1) ∨ (p3 ∨ p2)) ∧ p3) ∧ (p4 → ((p3 ∧ p1) → p3))) → (p5 → p2)) → p5)) ∨ (p3 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118115464982896600924066279385 : ((False ∨ ((((((True ∧ (p4 ∧ (p5 → p1))) → p2) ∧ p1) ∨ p4) → (((False → (p5 ∨ (False ∧ False))) ∨ p5) ∧ p4)) → p2)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2191709821278013622964518869 : ((((p3 ∧ (p3 → p1)) ∨ p4) ∨ ((False → p1) ∧ (p4 ∧ ((p3 → p1) → p4)))) ∨ (p2 → ((((p4 → True) ∨ p4) ∨ p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41222876157516724174934665248 : (((((((p4 ∨ (p2 → p2)) ∧ (p2 ∧ (p1 ∨ (p3 → p4)))) → p3) ∨ ((False → p4) ∨ p5)) ∧ (p3 ∨ (p4 → (True → p5)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789159389557807975672394923396 : (((p5 ∨ ((((p2 → (p2 → (((((p2 → p3) ∧ p5) → p4) → p5) ∧ p2))) → (p5 → (p4 ∧ p4))) ∨ False) → ((p4 ∨ p5) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805204553699862569195337400369 : (((p3 → (p3 ∧ ((p4 → (p1 ∨ (((p4 ∧ p3) → ((((p1 → True) ∨ (p1 ∨ p3)) ∨ p1) ∧ ((p3 ∨ p4) → False))) ∨ False))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41020002388781400527032871349 : ((((((p1 ∨ ((((p1 → True) ∧ p3) ∧ True) ∧ ((p2 ∧ p1) ∨ (p2 → p3)))) ∨ ((False → p5) ∨ False)) → False) → (p1 ∧ True)) ∨ p5) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ ((((p1 → True) ∧ p3) ∧ True) ∧ ((p2 ∧ p1) ∨ (p2 → p3)))) ∨ ((False → p5) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184977056218946484771832007307 : (((p5 ∨ (p1 ∨ p2)) → ((p3 → (p1 ∨ (p1 ∧ True))) ∨ p2)) ∨ ((((((p2 ∧ True) ∨ (p1 → p4)) → (p5 ∧ p5)) ∧ p2) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977972703896719946350478756178 : (((True ∧ ((p5 ∨ True) → (((p2 ∨ (p3 → p3)) ∨ (((p5 → ((p3 ∨ True) ∧ True)) ∧ p1) ∨ False)) ∧ ((False ∨ False) ∧ (p3 → p2))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246638909937575541512948227885 : ((p5 ∧ p3) ∨ ((((p2 ∨ p3) ∧ ((((False → True) → p4) ∧ p1) ∧ (p2 → p4))) ∨ p5) ∨ (True ∧ (True ∧ ((p5 → (True ∨ p4)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594243969691032194022754470576 : (((((False → (((((p4 → p1) → p1) → p3) ∧ (((p3 ∧ p2) → False) → True)) ∧ (p4 ∨ p2))) → (((False ∧ True) ∨ p5) ∨ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234421094935854849453112153826 : ((p2 → (True ∧ p3)) → (((((p4 ∨ (((p3 ∨ p5) ∨ p2) → False)) ∨ p4) → False) ∧ p4) → (p5 ∧ (p2 → ((p4 ∧ (p3 → p5)) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ (((p3 ∨ p5) ∨ p2) → False)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : ((p4 ∨ (((p3 ∨ p5) ∨ p2) → False)) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309648003423807359421513329376 : (p2 ∨ ((p2 ∧ (((((p1 ∨ p5) ∧ ((p5 → p4) ∨ (((True → True) → (True → p2)) → False))) ∧ p3) ∧ True) ∨ p2)) ∨ (True ∨ (p5 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135260630163497237928858927199 : (((p2 ∧ (p4 ∨ ((((False ∨ p4) ∨ ((((p5 ∨ True) ∨ p2) → p5) ∧ p3)) → (p1 ∧ p4)) ∨ True))) → (p5 ∨ False)) ∨ ((p3 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256116906192878054073220792581 : ((True ∨ p5) → ((True ∧ (((p1 ∧ (p4 ∧ p4)) ∧ p1) ∧ p5)) ∨ (True ∨ ((p1 ∨ p2) → (p2 → (p3 → (p1 ∨ ((True ∨ p5) ∧ False)))))))) := by
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
theorem thm_5_vars_56542544471232306691475855521 : (((p1 ∨ (p3 → (True ∧ p4))) → (((((((True ∨ p3) ∨ True) → False) ∧ p1) ∨ p3) ∨ (True ∨ ((p1 → True) ∧ False))) ∨ (p2 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787683530120816037139733817543 : (((p4 ∨ (p4 ∨ (p1 ∧ (((p4 → (p5 ∧ ((((p5 ∧ True) ∧ p4) ∧ p3) ∨ p3))) ∧ ((p5 ∨ (p2 ∧ p3)) ∨ p3)) → (p2 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156631259471407370266256198181 : (((((False ∨ (p4 ∨ p3)) ∧ (p3 → (((((p1 ∨ p1) → p4) ∨ p1) ∧ False) → True))) ∨ p2) ∧ p2) ∨ (p3 → (p4 ∨ (True ∧ (True → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8462977185851644301999422423 : ((((True → ((((p5 ∨ ((p4 → p1) ∧ True)) ∧ p4) ∧ (p5 ∨ True)) ∧ ((False ∨ ((p5 → (p5 → p4)) ∧ p3)) ∨ False))) → p3) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39676174628925462774473399961 : (((p4 ∨ ((((True ∧ ((((p4 → (p3 ∨ True)) ∧ (p5 → (p3 → p4))) ∨ p2) ∨ p3)) → p3) ∨ ((p5 ∧ False) ∧ False)) → p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58861247116436731545225098655 : (((True ∧ p5) ∨ ((((((p1 ∨ (True ∨ (p3 ∧ ((p2 ∧ p4) → False)))) ∧ True) ∨ (True ∧ p1)) ∨ p1) ∧ (p4 ∨ (p1 ∧ p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_940531727667554608510588396117 : ((((((p2 ∨ (False ∨ True)) ∧ p4) → True) → (True ∧ (((p1 → True) ∨ (((p1 ∧ ((p4 → p2) ∨ (True → p2))) ∨ p3) ∨ False)) ∧ p3))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ (False ∨ True)) ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231693379842072014090659584030 : (((p1 ∧ p4) → p2) → (p2 ∨ (((((False ∧ ((p4 ∧ (p2 → p4)) ∧ ((True ∧ False) ∧ (p3 ∧ True)))) ∨ p1) → p4) ∧ (p5 ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64977591213706340594556527543 : ((p2 ∨ ((((p3 ∨ p3) ∨ p2) ∧ False) ∨ (((True → (((True ∧ p4) → (((p3 → p3) ∨ p4) ∧ (p3 ∨ False))) → p2)) ∨ p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172706905851120356300983244277 : (((p1 ∨ p2) ∨ (((p1 → p5) ∧ (p4 → (p2 → (p2 ∨ p5)))) ∨ (p2 → False))) ∨ ((p4 ∧ (p4 → (p5 ∧ ((p2 → p3) ∧ False)))) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
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
theorem thm_5_vars_148017446375527371582553405750 : ((((p1 ∨ (((p2 ∨ (p3 → p4)) ∧ (p3 → False)) → False)) ∨ ((p2 → p2) ∨ (p1 → False))) ∨ (p5 → p2)) ∨ (True → (p5 ∨ (p2 ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_173152597914487404407564320317 : ((p3 ∨ ((p1 ∨ (p3 → p3)) → (False ∨ ((p4 ∧ False) ∨ ((True ∨ p3) ∨ p4))))) ∨ (p2 ∨ ((True → ((True → p2) ∧ (p5 ∨ False))) → p2))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184867304986481260196215345288 : ((((p1 ∧ p5) → p3) ∧ ((p2 → p4) → (p3 ∧ (p2 ∨ p2)))) ∨ (((p5 ∧ False) ∧ p4) → (p1 ∨ (p2 ∨ (p1 ∨ ((p2 ∨ p4) ∧ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645721958873744574871180609807 : ((((p5 ∨ (((p4 → ((p1 ∧ True) → p1)) ∧ False) ∨ ((p3 ∧ (p3 ∧ False)) → ((False → False) ∧ ((True ∨ p5) ∧ (p2 → p5)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40202576975819230045866176104 : (((((p4 ∨ p2) ∧ ((p1 ∧ ((p5 ∧ ((True ∨ ((False ∧ False) ∧ True)) → (p2 ∨ p5))) → True)) ∧ ((True → p5) ∨ p2))) ∧ p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219920807736154608526977577231 : ((p4 → (p4 ∧ (True → False))) → (((p1 → p5) → ((p5 ∧ (p4 → p4)) ∨ ((((p1 → p2) → p4) → (False ∨ p4)) ∨ (p4 → p4)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178231069038006605278741937546 : (((p3 → ((True → (((p3 ∧ p3) ∨ p5) ∨ p5)) ∨ (False ∨ p5))) → False) ∨ (((False → ((True → p4) → p2)) ∨ p3) → (p5 ∨ (p2 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335833681957300300301920084511 : (p1 → (((p5 ∧ (p3 → (False → ((p2 → ((p2 ∨ ((p5 → p4) → p2)) → False)) ∨ p4)))) → (p2 ∨ (p2 → (p4 ∨ (False ∨ p1))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229150604858150398194794169493 : ((True → (False ∨ p1)) ∨ ((True → ((p2 ∧ (False ∧ False)) ∨ ((p2 → p5) ∨ ((False → True) ∨ p4)))) ∨ (((p5 → (p3 ∧ p1)) ∧ p2) → p2))) := by
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
theorem thm_5_vars_42688465578994928341676979039 : (((p5 ∨ (((False ∧ (p4 → False)) ∨ ((True ∨ p2) ∧ (((False ∨ p3) ∧ (p5 ∨ ((p2 ∨ (p4 ∧ False)) ∧ False))) ∨ True))) ∨ p4)) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113112298983952331814878453003 : (((False → (((p2 → p2) ∨ (((False → p5) → p4) ∧ ((p5 ∧ (p4 ∧ ((p2 → (p5 → False)) → p5))) → p5))) → p2)) → False) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190826122941290726640359516762 : (((p3 ∨ (((p3 ∨ p1) → False) ∨ False)) ∨ (p3 ∧ p4)) ∨ ((p2 ∨ ((p1 → ((p5 ∨ p3) ∨ (p3 → p2))) → (p3 ∨ (True ∧ True)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41128135871887200111847889081 : (((((((p3 ∨ False) ∧ (((False ∧ False) ∧ (((False → (p5 ∧ p2)) ∧ True) ∨ p1)) ∨ p1)) ∨ p3) ∨ p4) ∨ ((False → False) ∧ True)) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138382615513092826509996273583 : ((p4 → ((p1 → p5) ∨ (((p5 ∧ False) → (False ∨ p3)) → ((p5 ∨ ((p5 ∧ p5) ∨ True)) ∧ ((True ∧ p3) → p5))))) ∨ (p5 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134092775110864464775785019396 : ((((p1 ∧ ((p5 ∨ (False ∨ p1)) → ((False ∧ (((p4 → (p4 → False)) ∨ p2) ∨ (p1 ∨ p3))) ∨ p2))) → False) ∨ p1) ∨ (False → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621218884614515508321298859925 : ((((True ∧ ((((False ∧ (p4 ∧ (False ∧ (((True → p4) ∨ (p3 ∨ (True ∨ (p5 → p5)))) ∧ False)))) → p5) ∨ (p5 ∧ p1)) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62673893588830922756350245743 : ((p4 ∧ ((False ∧ ((p5 ∧ ((False ∧ p3) ∨ (((p3 ∧ (p3 → (p1 ∨ p1))) ∨ ((p3 ∧ p3) → (False ∨ p3))) ∨ False))) → p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42658061336795686418194179638 : (((p4 ∨ (((p2 ∧ (((False ∨ ((p1 → True) ∧ False)) ∧ p1) ∨ ((True → p5) ∧ (p4 → p5)))) → p1) ∨ ((False ∨ p2) ∨ True))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180804754968933312246040167449 : ((((p4 ∧ True) ∨ p1) ∧ (((False → p5) ∧ (False ∨ (p1 ∨ True))) → p1)) → (p1 ∧ (p1 ∨ (p2 → ((p1 ∧ ((p3 ∨ True) → p1)) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((False → p5) ∧ (False ∨ (p1 ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : ((False → p5) ∧ (False ∨ (p1 ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301437987951904822085831310941 : (False ∨ ((p5 ∧ ((p5 ∨ p5) ∨ False)) → ((p1 ∨ (p4 → ((p3 → ((p2 ∧ (p1 → p4)) ∧ False)) ∨ (p3 → p5)))) ∨ (p1 → (p2 → p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63008915981489751911111490933 : ((p4 ∧ (p2 → (((p1 → ((False ∧ p5) ∨ ((p2 → (p2 ∨ True)) ∧ (p2 → p1)))) → (p1 ∨ (p3 ∧ (p1 → (p1 ∨ p5))))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115214574586208392902663891904 : (((p4 ∨ (p1 ∧ (p5 ∨ (p3 → (False ∧ (p4 ∨ p3)))))) ∧ (((((False → p3) ∧ (p3 ∧ (False → True))) → p2) ∧ True) ∨ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52003597212782753532613596335 : (((p1 ∧ ((False → (p5 → p5)) → ((True → ((p2 → p3) → p4)) → (True ∧ p1)))) ∨ ((p3 ∧ p3) → (p3 ∨ ((p4 ∧ p1) → p4)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172210535394913106031034157677 : (((((p3 ∨ p1) ∨ True) → (((p2 ∧ p2) → p1) ∧ p4)) → ((p2 → p4) → p4)) ∨ (p1 ∧ (p5 ∨ (((p2 ∧ p2) ∧ (False ∧ p5)) ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720241439668667046669628635742 : (((((p3 → (p1 ∨ p2)) ∧ p1) → (((True → (p2 → ((True ∧ p4) ∨ p2))) → (p4 ∧ p5)) ∧ ((True → p4) ∧ (p2 ∨ (True ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258798266762468336455387791324 : ((True → False) → ((p4 ∨ p3) ∨ (False ∨ (p5 → ((True ∧ (False ∨ (((p4 ∨ (p2 ∨ (p5 ∨ False))) → True) → (p2 → False)))) ∨ (False → p4)))))) := by
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
theorem thm_5_vars_174734282944744782260258605008 : ((((True ∨ p4) → p4) → (((True ∨ (p4 → ((True ∧ p2) ∧ p1))) → p2) → p5)) → ((p1 → p5) ∨ (False → (p2 ∨ ((p3 ∧ p3) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111871686356136073463401008325 : (((((p4 ∨ p2) ∨ ((p5 → (((p4 → p3) ∧ (False ∧ (False ∨ p1))) ∧ True)) → p5)) ∨ (p4 → (True ∧ (p2 → p4)))) ∨ p3) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247471627782938433699734268086 : ((False ∨ p3) ∨ ((True → (((p3 ∨ (((p1 ∧ p3) ∨ (True ∨ ((p1 ∨ (p2 ∨ p4)) → True))) ∧ p4)) ∧ (p2 → p3)) ∨ (p3 ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46907960845269181440620604556 : ((((((p5 ∨ ((p4 → p4) → (p1 ∨ p2))) ∧ (((False ∧ p5) → False) ∨ (p5 ∧ p5))) → ((True ∨ p2) ∧ p4)) ∨ p1) ∨ (False → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57263554589622568099097483872 : ((((p1 ∨ p2) → p1) ∨ (p2 ∨ (p1 → (((True ∨ (p2 ∧ (False → ((p4 ∧ True) → ((p5 → p3) ∧ (p5 ∨ False)))))) → False) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259309241483089131348514039575 : ((False → p2) → (((p2 ∨ (((True ∨ (p2 ∨ (p3 ∧ (((p2 ∨ ((p2 ∧ p3) → p4)) ∧ p5) → False)))) ∧ (False ∨ p4)) ∧ p4)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225918466064591635135163892978 : (((p2 ∧ True) ∨ p2) ∨ (p4 ∨ (p2 ∨ (True → (p1 → (((p3 ∧ p5) ∨ p3) ∨ ((((p1 ∨ p3) ∧ False) → p4) → (p5 → (p5 ∨ False))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



