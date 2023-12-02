variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352686590647079797461900064380 : (p4 → ((p3 ∨ p3) ∨ ((p5 ∨ (((p5 ∧ p2) ∧ True) ∨ p1)) ∨ (p2 → (p4 ∧ ((p4 ∨ (False → ((p4 → p4) → (p4 ∧ p3)))) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135496360888591017111595276124 : (((p1 ∧ (((p3 → p2) → (True ∨ p3)) → (p2 ∨ ((False → p1) ∧ ((False ∨ True) ∧ p3))))) → ((p5 ∨ p2) ∧ True)) ∨ (p5 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158729530005470414803107323889 : ((p3 ∧ ((False → p2) → (False ∧ (True ∧ ((((False ∧ (False ∨ p3)) → p4) → (p3 ∧ p1)) → False))))) ∨ (p4 ∨ (((p2 ∧ p5) ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137312924845820742251691332689 : ((p2 ∧ (((((p3 ∨ p1) ∨ (p4 → p5)) → p4) ∧ p1) ∨ ((True → (((False ∧ p3) ∨ (p5 → p5)) ∨ True)) ∧ p4))) ∨ (p4 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173120781147090479726019399732 : ((p2 ∨ (((True → p2) → (p3 ∨ p3)) → (((True ∧ False) ∨ (p4 → p5)) ∨ p4))) ∨ (((p2 ∧ ((False → False) ∧ p3)) ∧ p2) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58904329218596533296601752580 : (((False ∧ p5) ∨ (p4 ∧ ((p4 ∨ (False ∨ ((True ∧ ((p4 ∨ ((True ∨ True) ∨ ((p4 ∧ p4) ∧ p4))) ∨ (p1 ∧ p2))) ∨ True))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166521940240588193402552731530 : ((p4 ∨ ((True → (p5 ∧ False)) ∧ ((((p1 → ((p4 ∧ p2) → p5)) ∧ p1) ∨ p5) ∧ False))) ∨ (False ∨ (True → (((p1 ∨ True) ∨ p4) → True)))) := by
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
theorem thm_5_vars_218250016872529525280975263011 : (((False ∨ False) ∨ (p2 ∨ p2)) → ((True ∧ ((((p4 ∨ False) ∧ p3) ∨ p1) ∨ p3)) ∨ ((p5 → ((True → p1) ∨ (p1 → p1))) ∨ (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694267475812138787643418429123 : ((((((p4 ∧ p5) ∧ True) ∧ (p4 ∧ (p3 → ((True → (True ∨ True)) → p1)))) ∨ ((((False ∧ (p1 ∨ p2)) → p4) ∧ p3) → (p1 ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338851808860293674973440171654 : (p1 → ((p2 → p4) ∨ ((p1 ∧ ((((((p4 ∨ p2) ∧ ((True → False) ∧ p5)) ∧ p5) ∧ False) ∧ True) ∧ (p1 → (p5 ∧ True)))) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_207377807171320259392820532431 : (((True ∧ (p3 → (False ∧ True))) ∨ p4) → (((p3 → p3) → (p2 → (((p2 ∧ (p2 → (p1 ∧ (p4 ∧ True)))) ∨ (p2 ∧ p4)) → p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64514150162622611316421506489 : ((p1 ∨ (((p3 ∨ (p2 ∨ p1)) ∧ (p3 ∧ ((True → (False ∨ p2)) ∨ p5))) ∨ ((False → (p5 ∨ ((p5 ∨ False) → p5))) → (p4 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172028711746459830222198506953 : ((((p3 → True) → (False ∧ (((p5 → p3) → p1) → (p4 ∨ False)))) ∨ (p1 → p1)) ∨ ((False → ((p4 ∧ ((p1 → True) ∨ p3)) ∧ False)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119324329204617867080429592257 : ((p3 → ((False ∧ (((False ∨ p4) → (False ∧ True)) ∨ ((p4 ∧ p2) → True))) ∧ (((p5 ∨ (p3 → True)) → (p4 ∨ p2)) ∨ False))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115839018612193821482581866640 : (((p2 ∧ (p4 ∨ (p3 ∨ p1))) ∧ (((p4 ∧ ((p1 ∧ ((p5 → ((p1 → p4) ∧ p1)) → p2)) ∧ (p2 ∧ True))) ∨ False) → p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806024932248477808576059832167 : (((p4 → ((((True ∨ (True → True)) → p4) → ((((p2 ∧ p1) → (p3 → (((True ∨ False) ∧ p5) ∧ False))) → p3) ∨ (p3 ∨ p5))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247431688553725741555811777144 : ((False ∨ p2) ∨ ((p2 ∧ (((False ∨ p5) → (p4 ∧ (False ∨ False))) → p4)) → ((((((p5 ∨ p1) ∧ p5) ∨ (p1 ∧ p1)) ∨ p4) ∨ False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_323225195784018272258858622682 : (p5 ∨ (((((p4 ∨ ((p3 ∨ p1) ∧ p3)) ∧ p4) ∨ p3) ∧ (p1 → ((True ∧ (True ∨ ((p3 → (p4 ∧ p3)) ∨ p2))) ∨ p1))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199357015237562476266024467184 : (((((p1 ∧ True) ∨ p5) ∧ (p4 ∧ p2)) ∨ True) → (((True ∧ (p1 ∨ p3)) ∨ (True ∧ (p4 ∨ (((p2 ∨ p1) → p1) ∧ (True ∨ False))))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h4.left
      let h9 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h4.left
      let h12 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_921978359829294353609569012845 : (((((p2 ∧ (p4 ∨ ((p3 ∨ p4) ∨ (False ∨ (p1 ∨ p2))))) ∨ (p1 → True)) → (False ∧ (True ∧ ((((p3 ∧ p2) ∧ p5) ∨ False) ∧ p5)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (p4 ∨ ((p3 ∨ p4) ∨ (False ∨ (p1 ∨ p2))))) ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442877395643919006022209062882 : (((((((p2 ∧ (p3 ∧ p4)) ∨ (((p5 ∨ p3) ∧ (False → (p5 ∧ p3))) ∧ p5)) ∨ (p4 ∧ p5)) ∨ (True ∨ p4)) ∨ ((p2 → p4) ∧ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762410875967809046023120360628 : (((p3 ∧ ((p5 ∨ ((((p2 → p1) ∧ p5) → False) → (p2 ∨ ((p3 ∨ (p5 → (True ∧ (True ∨ p3)))) ∨ p3)))) → ((True ∨ p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196669073728284108543223220482 : ((((p1 ∨ ((p4 ∧ True) ∨ p4)) ∧ p5) ∧ p3) ∨ ((((False → p4) ∨ ((p5 → (False ∧ True)) → (p2 ∨ p3))) ∨ p2) ∨ ((p4 → True) → p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327059327806238858290604209820 : (True → ((((p2 → (True ∧ p1)) ∨ (p4 ∨ True)) → (True → (((((p5 ∨ p5) ∨ True) ∧ p4) ∧ True) ∨ ((False ∧ False) ∨ (True ∨ p5))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112821511065980362830907566403 : ((((p2 ∨ ((p2 → p2) ∧ p4)) ∧ ((p2 → p1) → (p4 ∧ (True ∨ (p2 ∧ ((p2 → False) ∨ ((p2 → p4) ∧ True))))))) → p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372158487091105775816594709 : ((p1 ∨ (((p3 ∨ p3) ∨ ((((((p1 → p4) ∧ p4) ∧ False) ∧ (((p2 → True) ∨ p5) ∧ False)) ∨ (True → (p3 ∨ p1))) → p5)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693832054511095303614880327496 : (((((((p2 ∧ p1) → False) ∧ ((p4 ∧ ((p1 ∨ p1) ∧ False)) → False)) → p4) ∨ ((((True ∨ p2) ∨ p3) ∧ (False → (True → p5))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133818744989075320573372784494 : ((((p1 ∧ p4) ∨ (((p5 → ((p3 ∨ ((p2 ∨ p4) → (True ∨ (False ∨ (True ∨ p3))))) ∧ p3)) → p5) ∨ False)) ∧ p1) ∨ (False → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685822442587470800675711472048 : ((((((((True ∨ p5) → (p2 ∧ (p4 → p2))) → p1) → (((p3 ∨ False) ∨ p2) ∨ p5)) → p2) → (((True ∧ p2) ∧ (p3 → p5)) → p2)) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666970992974239899897908445069 : (((((p5 → ((p2 ∨ True) ∨ p2)) ∧ (((p4 ∨ (p4 → (p4 ∧ True))) → (True ∨ p1)) ∧ (p4 ∨ (False ∧ True)))) ∧ ((p4 ∨ p5) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746454737257773957396024587063 : ((((p2 ∨ p3) → ((((((True → p5) ∨ ((p1 → (p5 ∨ ((p3 ∨ p4) ∧ p5))) ∨ False)) ∧ p1) → (p2 ∧ False)) ∧ (False ∧ p4)) ∨ True)) ∨ p3) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41945913294999019635484477000 : ((((False ∧ p4) ∧ (((p2 ∧ (p2 ∧ p5)) ∧ ((p4 ∧ ((True ∧ False) → (p2 ∨ p3))) ∧ p4)) → ((True → p4) → (p4 → p3)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218316551828306023413927267018 : (((True → False) ∨ (False → p5)) → (((True → (False ∧ (p4 ∨ p5))) ∨ (p2 ∧ p5)) → ((p2 → (True ∧ False)) ∨ (False → (p5 ∧ (p3 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h18
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234592521091777610591799932515 : ((p3 → (p2 ∨ True)) → (p4 ∨ (((True → p3) ∧ (True ∨ (((p2 → (((False ∨ p1) ∨ p5) ∨ p3)) ∨ (p2 ∧ (p3 ∧ True))) ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607055685848980746287901736451 : ((((((False → (((p5 ∨ (True ∨ p4)) → (True ∧ p2)) → (True → p3))) → ((False ∨ ((p5 ∧ (p4 → p2)) ∨ True)) ∨ p5)) ∧ False) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_156995398856271946952325964982 : ((((p2 ∧ (p4 → (p4 ∨ p2))) ∧ ((p4 ∧ (True ∧ True)) ∧ (p5 ∧ (True ∧ (p3 ∧ p2))))) ∨ True) ∨ ((p1 ∧ (p3 ∧ (p1 ∨ p1))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168754272512471689896023421418 : ((False ∨ (True ∨ ((p1 ∧ (p1 → (p2 ∧ (p3 → (p5 → (True ∨ (p3 ∧ p5))))))) → False))) → (((True → p5) → ((p4 → p1) ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_158188637583869231138802987956 : (((True → ((True ∧ p1) → p1)) → (True → (p4 ∨ (p4 ∧ (p5 → (((True → True) ∧ p2) ∧ p5)))))) ∨ ((True ∨ (p5 ∨ p2)) → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620421964812179827774959640767 : (((((p5 ∨ p1) ∨ ((((p4 → ((p1 → (True → p3)) ∧ (p4 ∨ p4))) ∨ True) → ((p4 → p1) ∧ (p4 ∧ p2))) ∧ (p4 → True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_112592501814575111143469964865 : ((((((p1 ∨ (p5 ∨ p3)) → p2) ∧ (False → ((False → p1) → (((False ∨ False) ∧ (False ∧ p1)) ∨ p5)))) ∧ (False ∨ p4)) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1499710023800149281663077369 : (((((False ∧ (p3 → ((p1 → False) ∨ ((p1 ∧ p1) ∨ (True → p2))))) ∧ True) ∨ (p3 ∧ False)) ∨ (p5 → (False → False))) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51418777910779986989048077724 : ((((p4 ∨ (((p5 ∧ ((p5 ∨ False) ∨ (p2 → False))) → p4) ∨ (p3 ∧ (True ∧ p5)))) → True) → ((True ∧ (p2 → p4)) ∨ (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232176232509439717432349597341 : (((False → True) → p1) → (p1 → (((p2 ∨ (((((p2 ∧ p2) ∧ p5) ∨ p1) ∧ False) → p4)) ∨ p4) ∧ ((((p3 ∨ p4) → True) → p1) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h12
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41246023094026949828382081700 : (((((((p5 ∨ ((False ∧ p4) ∨ True)) ∨ (True ∨ p2)) ∧ ((p2 → (p1 ∧ p4)) ∧ p4)) ∨ p4) ∨ (p4 → (p4 → (True ∧ p1)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319207129841252433892287214518 : (p4 ∨ ((((p5 ∧ (False ∨ (((False ∧ p4) → p5) ∧ True))) → p1) ∧ (((p1 ∧ True) ∧ p3) → True)) → (((p5 ∨ p1) → p4) ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_215118262656717852574194256802 : (((p3 → True) → (False ∨ p4)) ∨ ((False ∨ p4) ∨ (((p2 ∨ p1) ∨ ((p2 ∧ (p3 → True)) ∨ True)) ∨ ((p5 ∨ True) ∧ (p4 ∨ (False ∧ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613246942765206456163967709451 : ((((((((p1 ∧ (p5 ∧ (p2 → p1))) → (p5 ∧ p2)) ∧ False) → (((p3 ∧ p1) ∧ (p4 ∧ p1)) ∧ (p1 ∨ p4))) → (p3 ∨ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_785454500852977469421003614749 : (((p4 ∨ ((((True ∨ (p1 → p4)) ∧ ((p5 ∨ True) ∧ True)) → (((p4 → True) → (p4 → p5)) ∨ ((p2 → (p2 ∧ True)) ∨ True))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10495385186010206958046636443 : (((p2 → ((p5 ∨ (p4 → ((True → (True ∨ (False ∧ p3))) → (p1 → ((p1 → p4) → p3))))) ∨ (((False → p5) ∨ p5) ∨ p4))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14782606856646289080322160027 : ((((((((((p1 ∨ p5) ∨ ((True ∨ p4) ∨ True)) ∧ True) → p4) → p1) ∧ p3) ∨ True) ∨ (p4 ∨ ((p4 ∧ p1) ∧ p3))) ∨ (p2 ∧ p3)) ∧ True) := by
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
theorem thm_5_vars_41245671947762845503539320218 : (((((((False ∧ (p3 ∨ (p1 → (((p1 → False) ∨ p1) ∧ p3)))) ∧ p2) ∨ (p2 ∨ True)) ∨ True) ∨ (False → ((False ∧ True) ∧ True))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115898415365515406931518860045 : (((((p3 → True) ∨ p2) → p1) ∨ (p3 ∧ (p1 ∧ (((False ∧ p1) ∨ ((p4 ∧ True) ∧ ((p2 ∨ p1) → (p4 ∨ False)))) ∨ p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200760118550326722905514771951 : ((p4 ∧ ((p4 ∨ (p3 → (p4 ∨ True))) ∧ True)) → (((p4 ∨ (p3 → p1)) → ((True → False) ∨ p4)) ∨ ((p5 ∧ ((p5 ∨ p4) ∨ p3)) ∧ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33527956914713510988618048372 : ((p4 ∨ (True ∧ ((p3 ∨ (((p2 ∧ p3) ∧ (p1 ∧ p1)) ∨ ((((p2 ∧ p3) ∧ p1) ∧ (p3 ∧ (p2 ∨ p1))) → (False ∨ p2)))) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638009822844612542493801919112 : ((((((((p4 ∨ p5) ∨ p2) ∧ True) ∧ (True → False)) ∨ (p3 ∧ ((((p4 ∧ (p5 → (p3 ∨ True))) ∧ p1) ∧ (True → p4)) ∨ p2))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613886563448718941405701441933 : (((((((((False ∧ False) ∨ p4) ∨ (p2 → (((p4 ∨ True) ∨ p3) → ((p2 ∧ True) ∨ p3)))) ∧ p1) → False) ∨ (False ∧ (p5 ∨ p2))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_228924977867109337443629637218 : ((p4 ∨ (p2 ∨ False)) ∨ (((p2 ∨ p4) → (p3 ∨ True)) ∨ ((((True ∨ (p1 ∨ p5)) ∧ (p3 → p5)) → p1) ∧ ((p5 ∧ True) ∧ (True ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51138338217859581045248813341 : (((((((p2 → (True ∨ (p3 → p3))) → ((p1 ∨ True) ∧ p3)) → (p4 ∧ True)) ∨ p2) → p1) ∨ ((((False → False) ∧ True) → p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68498498699894485912806687062 : ((p3 → (p2 ∨ (((p3 → False) ∧ (p3 → p4)) → (((p1 ∨ ((p5 ∧ ((p3 → True) → p5)) ∧ p2)) ∨ p2) ∧ ((False ∧ p4) ∧ p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h17
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759260727975360395179627512707 : (((p2 ∧ (((p1 → (p1 ∧ ((True ∧ p1) ∧ (p2 ∨ ((p4 → (p3 ∨ p2)) ∧ (p1 → True)))))) ∧ (p2 ∨ (p5 → p3))) → (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215870499850411052712282089571 : ((p2 ∨ (p1 → (p2 ∧ p5))) ∨ (p3 → ((True ∧ ((p3 ∧ (p1 → p5)) ∧ (p5 ∨ (False ∧ p2)))) ∨ (p5 → (p2 ∨ ((False ∧ False) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52791352282323213142588403301 : ((((p1 → ((False → (p5 → p1)) ∨ (False → (p5 ∧ p2)))) → (p4 ∧ p5)) → (((True → p1) ∨ ((True ∧ (True ∧ p1)) ∨ p5)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134611318544529427301191979025 : (((((((p2 → ((True ∧ ((False ∨ p5) ∨ (p3 ∨ p1))) ∧ True)) ∨ p2) → p1) ∧ p2) ∨ ((p2 ∨ p2) ∨ p3)) → p4) ∨ (False ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157250034742270416966044785424 : ((((((p5 ∨ p2) ∨ True) → (p2 ∨ False)) ∨ (p3 → (False ∨ ((True ∨ (p4 ∨ p3)) → p4)))) → p3) ∨ (p3 → (p3 → ((True ∧ p3) ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309340753424059728188464080813 : (p2 ∨ (((((p4 ∨ p3) ∧ p2) ∨ ((p5 → p4) ∨ ((((p3 → p1) ∨ False) → (p5 → False)) → True))) ∨ ((False ∧ p5) → False)) ∨ (p3 ∧ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46984742473521141741591796239 : ((((((p5 ∨ ((p4 → False) → ((True ∧ ((p4 ∧ p4) ∨ p3)) → (False ∨ True)))) ∨ p4) → (False → (False → p4))) → p2) ∨ (True ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264611587105187679824781734616 : (True ∧ (((p2 ∧ True) ∨ p1) → (((p2 ∨ p4) ∨ ((p3 ∧ p2) ∧ (p3 ∧ (p1 ∧ (p2 → (p5 → (((p5 ∧ False) ∨ p2) ∧ p3))))))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172598516126054431235528122431 : (((p1 ∧ (p5 ∨ p3)) → (p5 ∨ ((p5 ∨ True) ∧ (p2 ∨ (True ∧ (p2 ∨ False)))))) ∨ ((((True → p2) → p3) → ((p5 ∧ p4) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232392873238220291209784001326 : (((p5 → p2) → p5) → (((False ∨ p2) ∧ p5) → ((True ∨ (p5 → p5)) → (((((True ∧ (False ∧ p1)) → p1) → p3) ∨ (True ∨ p2)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h2.left
    let h21 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56461537307985590965586947881 : ((((p1 ∧ p2) → (p3 → p1)) → ((p2 ∧ ((False → (p2 → p5)) ∨ (((p1 → (((p3 ∧ p2) ∨ p5) ∨ p3)) ∧ False) ∧ p4))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113694655491224167147026509214 : ((((((p2 → (False ∨ p4)) ∨ p2) → (((p5 ∧ (p5 → (True → True))) → ((p1 ∨ p4) ∨ p2)) ∨ p1)) → p4) → (p2 ∧ p4)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336168174778373206117524286506 : (p1 → ((((False → (p5 ∧ p1)) ∧ (p1 ∨ ((((False → (p4 ∨ False)) ∨ (p5 ∧ (p5 ∧ True))) ∨ (p5 → p3)) ∧ (p1 ∧ p1)))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248591402650861506463189181179 : ((p3 ∨ False) ∨ (((p3 ∧ True) ∧ p2) ∨ ((((p4 ∨ (False ∧ p5)) → (p4 → ((p4 ∧ (True → False)) ∨ True))) → (p2 ∨ False)) ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_318641664160718747748687307792 : (p4 ∨ ((p1 ∨ (((p1 ∧ p3) ∨ ((p1 ∨ True) ∨ p2)) → ((((p4 ∧ p4) ∨ ((False → p5) ∧ (p2 ∨ p3))) ∧ p1) ∧ p1))) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315153286445115733248174623180 : (p3 ∨ ((((True → (p4 → p3)) → p1) → p2) → ((p1 ∨ ((p4 ∧ (p2 ∧ p4)) ∧ ((True ∨ p3) ∨ True))) → (False ∨ ((p1 ∨ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305352885257713951960468563768 : (p1 ∨ ((False ∨ ((True ∨ ((p1 → p4) ∨ p5)) ∧ (((p3 ∧ True) → (True ∧ (p1 ∨ p5))) ∨ True))) → (p1 ∨ ((p2 ∧ (p4 ∨ p4)) → True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h13 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231977911552857060300294389680 : (((p2 ∨ True) → False) → (((p1 ∧ (p1 ∧ True)) ∨ ((((p4 → ((p2 ∧ p3) ∧ True)) → ((p5 → False) ∧ (True → p2))) ∨ p4) ∧ False)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122190622385517210149401548268 : ((((((((p3 → (False ∧ p5)) → ((p2 → True) → p3)) ∨ (p2 → p4)) ∧ p5) ∧ True) ∨ (p3 ∧ (p5 → True))) ∧ (True ∨ p4)) → (p1 ∨ True)) := by
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
      cases h3
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
theorem thm_5_vars_55606969190085150133375729135 : (((False → (True ∨ ((p5 ∧ True) → p2))) → (((False ∨ (((p5 ∨ p4) → p5) ∨ ((True ∧ p5) → (True ∨ (p5 → p1))))) ∨ False) ∨ False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157344923492857364001144352610 : (((p4 ∨ ((p1 ∨ ((p4 → p2) ∧ (p4 ∨ ((p3 → p3) ∧ (p2 → (p3 ∧ p1)))))) → p5)) → p3) ∨ (p4 ∨ (((p3 → p2) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157264416359925355984632901574 : ((((p4 ∨ ((p4 ∧ False) ∧ p2)) → (p5 → (p1 ∧ ((p5 → ((p3 → p2) ∧ p4)) → p2)))) → False) ∨ (True ∧ (True → ((p4 ∨ p4) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114821043860314956828186385814 : (((p3 ∧ (((True ∧ (p4 → p5)) ∨ p1) ∨ ((p5 ∨ p2) ∧ (p5 → False)))) ∧ (p2 ∨ (((p4 → (True ∨ True)) ∨ p5) ∧ False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231828854074567540695816192072 : (((p5 ∧ False) → p3) → ((True ∧ (p3 ∧ ((p3 ∧ (p1 ∧ p1)) ∨ (p3 ∨ p5)))) ∨ (p5 ∨ (p4 → (((False → p1) ∧ (p4 ∨ False)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177773632984777449218524107630 : (((p1 ∧ ((((True ∧ p1) → False) ∧ p3) ∧ ((p4 ∧ False) ∨ p5))) ∧ False) ∨ (p1 → ((p2 ∨ (((True → p5) ∨ p3) ∧ (p1 ∧ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50401591677227903639719660170 : ((((p4 → p1) → ((p5 → (p5 ∧ (((p4 ∧ (p2 ∧ ((p2 ∨ p3) ∧ p5))) ∧ p4) ∨ p2))) ∨ False)) ∨ (p1 ∨ ((p3 ∨ True) ∨ p5))) ∨ p2) := by
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
theorem thm_5_vars_922858829194070998306617071637 : ((((p2 → ((p5 ∧ p5) → (((p5 → (False ∨ (p3 → p2))) ∨ p1) ∨ p4))) → (p2 ∧ ((p1 ∨ (((True ∧ p5) ∨ p4) ∨ p2)) ∧ False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p5 ∧ p5) → (((p5 → (False ∨ (p3 → p2))) ∨ p1) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305615323588936871853894892425 : (p1 ∨ (((((p3 → True) ∧ ((p5 ∨ False) → p4)) ∨ False) ∨ (True → p4)) → ((p5 ∨ (((p5 ∧ p3) ∧ (True → True)) → (p1 ∨ p4))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : (p5 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h20
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123740361599909471440770106806 : ((((p3 ∧ p3) ∨ ((False → True) → (((p5 ∧ p5) → True) ∧ (p2 ∧ p2)))) ∧ (((p3 ∨ p2) → False) ∧ (p3 → (p3 ∨ p1)))) → (p5 ∧ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h15 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h17 := h11 h15
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h20 := h12 h14
    -- False on the left can always be used.
    apply False.elim h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h22.left
    let h27 := h22.right
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h28 : (p3 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h29 := h26 h28
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h22.left
    let h32 := h22.right
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h33 : (p3 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h34 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h36 := h30 h34
      -- We need to get the right conjuct of h36 based on <expert-advice>.
      let h37 := h36.right
      -- We need to get the left conjuct of h37 based on <expert-advice>.
      let h38 := h37.left
      -- One of the premise coincides with the conclusion.
      exact h38
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h39 := h31 h33
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42661265522128787971680991523 : (((p4 ∨ ((((p5 ∨ True) → (True → False)) ∧ (((p4 → p2) ∧ (p3 ∧ p1)) ∨ p3)) → (((True ∧ (True ∨ p5)) ∧ p5) ∨ p2))) ∨ p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p5 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71230561452863400695888067395 : ((((True → (False ∧ p3)) ∧ (((p1 ∧ p4) ∧ ((True ∨ p4) → (True ∧ ((True ∧ (p2 → True)) ∨ p1)))) ∧ ((p2 ∨ p5) ∨ False))) ∧ p4) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702427554995245212222956005328 : ((((((p5 ∨ p1) → ((p3 ∨ p1) ∨ (p2 → p4))) ∨ p2) ∨ ((((False ∧ (True ∨ p2)) ∨ (p1 ∧ p4)) → False) → (p4 ∧ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51867744198406337161569770404 : (((((((p4 → p1) ∨ p3) ∧ (False ∧ p3)) ∨ (p3 ∨ (p4 ∨ (p5 → p5)))) ∨ False) ∨ (p5 ∨ ((p3 → (p1 ∨ (p4 ∧ True))) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_689084287560733444925428252194 : (((((p4 ∧ (((p4 ∨ (False → False)) → ((p2 ∨ (p4 ∨ p2)) ∧ p2)) ∧ p4)) ∨ False) ∨ ((p4 ∨ p2) → ((p1 ∧ p4) ∨ (p2 → True)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353343151645899581464141051367 : (p4 → (False ∨ (((((((p5 ∨ ((p5 ∧ p1) ∧ p1)) → ((p4 → (p3 → p1)) ∧ p2)) → (p2 ∨ False)) ∧ (p4 ∨ True)) ∨ p4) ∧ True) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68960793223101184296183385170 : ((p4 → (p2 → (((p1 ∨ (False → (((p3 ∨ True) ∨ ((p2 ∨ p2) ∨ (p4 ∨ (p4 ∧ p1)))) → ((p4 ∨ p1) ∨ p2)))) ∨ p1) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259755066467684297339848963367 : ((p1 → p2) → (((((((p4 → ((p5 ∨ p1) → False)) → True) ∨ p3) → (p1 ∨ p2)) ∧ p1) → False) ∨ ((False ∧ p4) → (p1 ∧ (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59013430631192757979949165581 : (((p3 ∧ p4) ∨ (((((p4 ∧ p1) ∧ ((p4 ∨ True) ∧ p2)) ∨ ((((True → p4) ∨ p4) → (p3 ∨ (False ∧ p5))) ∧ p4)) ∧ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134495141370722828517822815299 : (((((p3 ∧ (((p3 → (p1 ∨ False)) ∨ (p4 → (((False → p2) ∨ p5) ∧ p2))) ∧ True)) → (p1 ∨ True)) ∨ p1) → p1) ∨ ((p5 ∧ False) → p1)) := by
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
theorem thm_5_vars_301301308773790326033849466131 : (False ∨ ((p4 ∧ (True → ((p2 ∧ p5) ∧ p3))) → ((((p2 ∧ p3) ∨ True) → (True → (((p4 ∧ True) ∨ (p1 ∨ p2)) ∧ (p1 ∨ p1)))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237892331489542290190468425447 : ((True ∨ True) ∧ ((((p4 ∧ (((p4 → p3) ∧ (p5 → (p2 ∧ (p5 ∨ p5)))) → p5)) ∧ True) ∨ p1) ∨ ((True ∧ p3) → (p5 → (p2 → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



