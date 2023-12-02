variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113520528401692875201947511963 : ((((p5 ∨ ((p5 ∨ p1) → (((p4 → True) ∧ p1) ∧ True))) ∨ (p2 ∨ (p2 ∨ (False ∧ (p1 ∧ (p4 ∨ True)))))) ∨ (p2 → p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701549343540764243466789446627 : (((((False ∧ False) ∧ (p4 ∨ (p5 ∨ (False ∨ (True ∨ p1))))) ∧ (p5 ∨ (((((((True ∨ p3) ∧ True) ∨ False) → False) ∧ p5) ∨ p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179431696865687498753161995790 : ((p4 ∨ (p4 ∧ (((p3 → True) ∧ p1) → ((p3 ∧ (p2 ∧ p1)) ∧ True)))) ∨ (p1 → ((((p2 ∨ p2) ∨ True) → (p2 ∨ (True → p4))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260939996601402182409621993307 : ((p4 → False) → (p2 → (((((p2 ∨ False) ∧ (p2 → (True ∨ False))) → (p2 ∨ True)) → ((p2 ∧ True) ∧ p1)) ∨ (p5 ∨ (True ∧ (True ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56629624803603492404255954973 : ((((p3 ∧ p5) ∧ p2) ∧ ((p1 ∧ p2) ∧ ((p3 → (p3 ∨ p1)) ∨ (((False ∧ (p5 ∧ p4)) ∧ ((p1 ∧ p2) ∧ (p3 ∧ p1))) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94632858234058757012944210557 : ((p3 ∧ ((((p3 → (p2 ∨ ((p1 ∧ p3) ∧ (p1 → ((p5 → p1) ∧ ((p1 ∧ p5) ∨ False)))))) ∧ (True ∧ p3)) ∨ (p1 → True)) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 → (p2 ∨ ((p1 ∧ p3) ∧ (p1 → ((p5 → p1) ∧ ((p1 ∧ p5) ∨ False)))))) ∧ (True ∧ p3)) ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40816949994187810065628404028 : ((((p4 ∨ (((((False ∨ (p2 ∧ False)) → (p4 ∧ p3)) ∧ p1) ∧ p5) ∧ (((True → (p5 → p2)) → True) ∧ (p1 ∨ p1)))) → p4) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166749673234684395915393187276 : ((p4 → ((p1 ∨ (p5 ∨ p2)) ∨ (((True ∨ (p2 ∧ p2)) ∧ p2) → (True ∧ (p2 ∧ p5))))) ∨ (True ∨ ((False → p3) → (p1 ∨ (p5 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353560890678945236144405630364 : (p4 → (p3 ∨ ((p2 ∧ ((p4 ∧ False) ∧ True)) ∨ ((p1 → (((p3 ∨ p5) → (p4 → (p5 → False))) ∧ (p1 → (p1 ∧ p5)))) ∨ (p4 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226319835059424161753973062234 : (((p5 ∨ False) ∨ p5) ∨ (((p4 → (True ∨ p3)) ∨ (False → p5)) ∧ (((p3 ∨ (((p3 → (p3 → p1)) ∧ (False ∧ p3)) ∨ p1)) ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119082087112544500036809186757 : ((p1 → (((False → (((p2 → p2) ∨ (p4 ∧ ((p5 ∧ p2) ∨ False))) ∧ (p5 ∧ p1))) → False) ∨ ((p2 ∧ p1) ∧ (True ∧ p3)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747291467381118908188533319692 : ((((p5 ∨ p3) → ((((p3 → (p5 ∨ True)) ∨ ((((((True ∨ p1) → p4) → True) ∨ p2) → p4) ∧ p2)) → p5) ∨ (False ∨ (False ∨ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114037430982893462260378343859 : ((((p1 → ((p1 → False) ∧ (((p1 ∨ ((True ∨ (False → (p2 ∨ False))) ∧ p4)) → False) → p4))) → p2) ∨ (False ∨ (False → p4))) ∨ (False ∨ p5)) := by
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
theorem thm_5_vars_149065666471368132414290538144 : ((((p5 → False) ∧ True) → (((p2 → (True ∧ (p1 ∧ (False → ((p4 ∨ p5) ∧ p1))))) ∨ p3) → (p1 ∧ p1))) ∨ (((False ∨ p2) ∧ True) → p2)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355558894496523135653727870880 : (p5 → (((p4 → (p4 → ((p4 ∨ (True ∨ (((p3 ∧ ((False ∨ True) ∧ True)) ∨ ((p3 ∧ p4) ∨ p1)) → False))) → p5))) → p2) ∨ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138301443208376050024645383729 : ((p3 → (((((False ∨ ((False ∧ p3) → p5)) ∨ p1) → p5) → (False ∨ p1)) ∨ ((True ∧ ((p4 → p1) → p3)) ∨ False))) ∨ ((p1 ∨ True) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349959797842853575947961390676 : (p4 → ((((p1 → (p4 ∨ p4)) → (True → (((False ∧ ((True → True) → False)) ∨ ((p2 → ((True → p2) ∧ p4)) ∧ p2)) ∨ p1))) ∧ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214179988329679222536411922125 : ((((False ∨ p4) → p2) → p1) ∨ ((((p2 ∨ p3) → (((((p3 ∨ p2) ∨ p2) → p4) → (True ∧ (False ∧ p2))) → (p5 ∨ True))) ∨ p3) ∨ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_714931385661553331348252063476 : ((((p5 ∧ (p5 ∧ ((p5 ∨ p4) → False))) → (((False → (False ∨ p2)) ∧ p4) ∨ (((False ∨ (((p5 ∧ False) → p1) ∨ p1)) ∨ p1) → p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50669899624373748205264617343 : ((((False ∧ ((p4 ∧ p5) ∧ (p4 ∧ p5))) ∨ (((False ∨ (p2 ∧ (p2 → p2))) → (p4 → p4)) ∨ False)) → (((True ∨ p4) ∨ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343613845700802309163585655667 : (p2 → (True ∧ (((p4 ∧ (p4 ∨ ((((p4 ∨ True) → False) ∨ (True ∧ p3)) ∧ p1))) ∨ (True → ((((False ∧ True) → p5) → p2) ∨ False))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137265217691883451672727191691 : ((p1 ∧ (p4 ∧ (((False ∨ (((p3 ∧ True) → p4) ∧ ((p3 ∨ True) ∧ (p1 → p4)))) ∧ (True ∧ (p5 ∨ p1))) → p1))) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_608401460590163741938037481426 : ((((((p4 → (p3 → ((False ∧ ((((p5 ∨ ((p4 ∨ p4) ∧ p2)) ∨ False) → p3) → ((p2 ∧ p2) ∧ p4))) ∨ p5))) ∨ p2) ∨ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_672706615120167548862154084018 : (((((((False → ((((p4 ∧ p1) ∧ False) → (((p3 ∧ p2) ∧ True) → p5)) → p2)) ∨ p5) ∧ p3) → (True → p4)) → (p3 ∧ (p5 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231167581564330815777579681930 : (((p2 ∨ p2) ∨ True) → ((((p5 ∧ ((((((p1 ∧ (True → p2)) → (p3 → True)) ∧ p4) → False) ∨ False) ∨ p5)) ∨ False) ∨ True) ∨ (p5 → True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134222594402079094957597222133 : (((((p3 ∨ ((p4 ∨ p2) → p5)) → False) ∨ (p5 → (((p5 ∨ False) ∧ (True ∨ (p2 → True))) ∨ (p1 ∨ p3)))) ∨ False) ∨ ((p3 → p5) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172467333722566840099933843567 : (((p4 → ((p4 ∧ True) → p3)) ∨ ((((p1 → p2) → p2) ∨ (p4 → p5)) → p1)) ∨ (False → ((p5 ∧ (p4 → True)) ∧ ((False ∧ False) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594489867319693965146866193295 : ((((((((False ∧ ((p2 ∨ p5) ∧ ((p4 → True) ∨ p1))) ∨ p2) ∧ p1) ∧ (True ∧ p2)) ∨ ((p2 ∨ (p3 ∨ (p5 → p3))) ∨ True)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670624574119061977856782948712 : (((((p2 ∧ True) → ((((((False ∧ (p4 ∧ (p1 ∨ p4))) ∧ p4) ∧ (p5 ∨ p5)) ∨ p3) ∨ p5) ∧ (p3 ∨ p1))) ∨ ((p3 ∨ True) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_136851283834693344735116931040 : (((p4 ∧ False) ∨ ((((p4 → (p5 ∨ (p4 ∨ p1))) → ((((p2 ∧ (True ∨ p5)) ∧ p5) ∧ True) ∨ p1)) ∨ p2) ∧ p5)) ∨ ((True ∨ p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110755518798539122121890560364 : ((((p3 ∧ ((p1 ∧ (True ∨ ((p3 ∨ p2) ∧ (p4 ∧ (((p4 → p4) ∧ False) ∧ (p5 ∨ (p3 ∧ p4))))))) ∨ p1)) ∧ p2) ∧ p5) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_571563331181390015557262453385 : (((p1 → (((p3 ∨ ((p3 → (p3 ∧ ((p1 ∧ p4) → ((p5 → p1) → p2)))) ∨ (p2 → (p4 ∨ True)))) → False) → ((p2 ∨ p5) ∧ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ ((p3 → (p3 ∧ ((p1 ∧ p4) → ((p5 → p1) → p2)))) ∨ (p2 → (p4 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ ((p3 → (p3 ∧ ((p1 ∧ p4) → ((p5 → p1) → p2)))) ∨ (p2 → (p4 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158453624390029781305343337350 : (((True → False) ∨ ((True ∧ p3) → (False ∨ ((((p3 ∧ p4) ∧ (True ∨ p3)) ∧ (p1 ∧ False)) ∨ p3)))) ∨ ((p5 → p5) → ((True → p4) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299146628891531217176155631361 : (False ∨ ((((p3 → p4) ∧ (((((((p3 ∧ (p1 → True)) ∨ False) → (p5 ∨ p5)) ∧ True) ∨ p3) ∨ ((p2 ∧ p5) ∧ p1)) → p3)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172498311342115133147567616609 : (((p4 → (p3 ∧ (p5 ∧ p3))) → ((False → ((p3 → False) → False)) ∧ (p1 ∨ p1))) ∨ ((p4 ∨ p5) → (p4 ∨ (p1 → (True ∨ (p5 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226057666887446083911922343121 : (((p5 ∧ p3) ∨ p1) ∨ ((p5 ∨ ((((p4 ∨ ((p2 ∧ False) ∧ p1)) ∧ (p1 → False)) → (p3 ∧ p5)) ∨ (((False → p1) → True) ∧ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66498545496880965346566311560 : ((True → (((True ∨ p4) → (((p1 ∨ ((False ∧ p5) ∧ p5)) ∧ ((p5 ∧ (p2 ∧ ((p2 → p3) ∧ False))) → False)) ∧ (p1 → p4))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160956163199566207808468122087 : ((((p2 ∧ p2) → p4) ∧ ((p2 ∨ (p3 → (p5 → (p1 ∨ p2)))) → ((p5 ∨ (p1 ∨ p3)) ∨ p4))) → ((p1 → (True → (True → p3))) ∨ True)) := by
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
theorem thm_5_vars_43915224326267800545109962934 : (((((p1 → ((((False ∧ ((p4 ∨ p1) → True)) ∨ False) → (p3 ∧ (p1 ∨ (p3 ∨ (p1 ∧ p3))))) ∧ p3)) ∨ False) ∨ (p1 ∧ p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338242396580539862368367777892 : (p1 → (((p1 → False) ∨ (p4 ∧ (True ∨ p3))) ∨ ((False ∧ (((p2 ∧ (p4 → p5)) ∧ p3) ∨ (((p4 → (True ∨ p4)) → p4) ∨ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319025565975638644942594107835 : (p4 ∨ ((((p1 ∨ (p1 ∨ p1)) ∨ ((False ∨ True) → ((p2 → ((p3 ∨ (p3 ∨ p1)) ∧ p5)) → False))) ∧ p1) ∨ (False → (p1 → (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705126938223038566444750822197 : ((((((p2 ∨ ((p2 ∧ p1) ∧ p5)) ∧ p2) ∧ True) ∧ (((((p2 ∧ (p4 ∧ p2)) → (p2 ∨ True)) ∨ (p2 → (p5 ∧ p3))) → True) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43527877511820967253285449677 : ((((False → ((((False → (False ∨ True)) ∧ p4) → (p1 ∧ (p1 → (True ∨ (False → (True ∧ p5)))))) ∨ (p4 ∧ (p5 ∨ False)))) ∨ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37648054545315261728514643803 : (((((p4 → (p1 → (p1 ∨ ((p3 → (False → p2)) → (((p3 ∧ (False ∨ p5)) → ((p2 ∧ p3) → p5)) ∨ True))))) ∨ p2) → p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758836515548950679155071987727 : (((p2 ∧ ((((((True ∧ p1) → p2) ∨ (False ∧ ((p1 ∧ p4) → ((False → p5) ∨ (p4 → (p2 ∨ p2)))))) → (p1 ∨ True)) ∨ True) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311768216538226197719905535473 : (p2 ∨ (False ∨ ((p5 → ((False ∧ ((p3 ∨ p1) ∧ False)) ∨ True)) ∨ (p3 → (p3 ∨ (((p3 ∧ False) → ((p3 ∧ p1) ∧ (p2 → False))) ∨ p5)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255849376682861066595230866798 : ((True ∨ p1) → (((False ∨ ((p3 ∨ p4) → (p4 ∧ (((p5 ∧ ((p4 → p5) ∨ p5)) ∧ (True → p1)) ∧ p5)))) ∨ (p1 → (True → True))) ∨ False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168181098001555449345549327969 : (((True → (False ∧ p2)) ∧ (((False ∧ (p1 → (p3 ∨ p1))) → p4) ∨ ((p1 ∧ p4) ∧ p2))) → (((p1 ∧ (p4 ∧ (p5 ∧ p3))) ∧ p4) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h28 := h24 h27
    -- We need to get the left conjuct of h28 based on <expert-advice>.
    let h29 := h28.left
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h35 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h36 := h24 h35
    -- We need to get the left conjuct of h36 based on <expert-advice>.
    let h37 := h36.left
    -- False on the left can always be used.
    apply False.elim h37
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h39
  case inl h40 =>
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h41 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h42 := h38 h41
    -- We need to get the left conjuct of h42 based on <expert-advice>.
    let h43 := h42.left
    -- False on the left can always be used.
    apply False.elim h43
  case inr h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Conjunctions on the left can always be decomposed.
    let h47 := h45.left
    let h48 := h45.right
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h49 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h50 := h38 h49
    -- We need to get the left conjuct of h50 based on <expert-advice>.
    let h51 := h50.left
    -- False on the left can always be used.
    apply False.elim h51
  -- Conjunctions on the left can always be decomposed.
  let h52 := h1.left
  let h53 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h53
  case inl h54 =>
    -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
    have h55 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h52, we can now drive its conclusion.
    let h56 := h52 h55
    -- We need to get the left conjuct of h56 based on <expert-advice>.
    let h57 := h56.left
    -- False on the left can always be used.
    apply False.elim h57
  case inr h58 =>
    -- Conjunctions on the left can always be decomposed.
    let h59 := h58.left
    let h60 := h58.right
    -- Conjunctions on the left can always be decomposed.
    let h61 := h59.left
    let h62 := h59.right
    -- One of the premise coincides with the conclusion.
    exact h62
  -- Conjunctions on the left can always be decomposed.
  let h63 := h1.left
  let h64 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h64
  case inl h65 =>
    -- We want to use the implication h63 based on <expert-advice>. So we show its premise.
    have h66 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h63, we can now drive its conclusion.
    let h67 := h63 h66
    -- We need to get the left conjuct of h67 based on <expert-advice>.
    let h68 := h67.left
    -- False on the left can always be used.
    apply False.elim h68
  case inr h69 =>
    -- Conjunctions on the left can always be decomposed.
    let h70 := h69.left
    let h71 := h69.right
    -- Conjunctions on the left can always be decomposed.
    let h72 := h70.left
    let h73 := h70.right
    -- One of the premise coincides with the conclusion.
    exact h73



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621121403063220882060492757846 : (((((p4 → p2) → ((True → False) ∨ (p3 ∨ ((((p3 ∨ (p3 ∧ False)) ∨ p3) ∧ ((p2 ∧ p5) ∨ (False → p4))) ∨ (p1 ∧ p5))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_180236099559482956717718212453 : (((p3 ∧ ((((False ∨ p1) → (p5 → p4)) ∧ (p2 ∨ p4)) ∨ p3)) → False) → ((((False → p5) ∧ ((p4 ∧ True) ∨ p1)) ∧ p5) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_638733244576656049008155293515 : ((((((p4 ∨ p4) → (True ∨ (p2 ∨ p4))) → (p3 ∧ (((False ∨ ((p3 ∨ p4) → (((p4 ∧ p3) → True) ∧ p5))) ∧ False) → p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136504795172907527040405933741 : (((False ∧ (p2 → p2)) ∧ (((p3 ∧ p4) → (((True → (True ∧ p1)) ∧ True) → True)) → (((p2 ∧ p1) ∨ False) ∧ False))) ∨ (p1 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89302361305926234425815502863 : (((False ∨ (p3 → p5)) ∧ ((((True ∨ ((True ∧ (False ∨ ((False ∧ (False ∧ p3)) → False))) → p2)) ∧ ((p2 → p4) ∧ p3)) ∨ False) ∨ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h9.left
          let h12 := h9.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h13 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h14 := h5 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h9.left
          let h17 := h9.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h18 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h19 := h5 h18
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260999700272145168843652129268 : ((p4 → p1) → (p1 → (((((p1 → p1) → (False ∨ p2)) ∨ p5) ∧ (p3 ∧ ((p5 → (((p3 ∧ p2) ∧ (p4 ∧ True)) ∨ p5)) → p5))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186671628496327935665150676318 : ((((p2 ∨ p1) ∨ (p4 ∧ (p4 ∧ p5))) ∧ ((p3 ∨ p4) ∧ p5)) → ((p3 → p4) ∨ (p4 ∨ ((((p1 ∨ False) ∧ (p3 ∨ p4)) ∨ True) ∨ p3)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179218328204630070435048233788 : ((p4 ∧ (((True ∧ p2) ∨ (True ∧ p2)) ∧ (((p2 ∧ True) ∨ False) ∧ p5))) ∨ (p2 ∨ (p5 ∨ (((p5 ∧ True) ∧ p2) → ((p2 ∧ p2) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355568334371752398803991013453 : (p5 → (((p4 → ((p2 → True) ∨ (((p3 ∧ ((p2 ∨ p4) ∧ ((True → p4) ∧ False))) ∨ (p3 ∧ p3)) ∧ False))) → (p5 ∧ p2)) ∨ (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200324938116563890151532447553 : (((False ∨ True) ∧ (((p5 → p1) ∨ True) → False)) → ((((True ∨ (False ∧ False)) ∧ (True ∨ False)) → (p4 → (p2 ∧ (True ∧ p1)))) → (p5 → p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((p5 → p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654405580214945105325572302369 : (((((((p5 ∨ True) → (p5 ∨ False)) ∧ ((p3 ∨ ((((p4 → (p5 ∨ (p4 ∨ p2))) → p3) → p5) → p2)) ∨ True)) ∨ p1) ∨ (True ∨ p2)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_347120379053143004131403499855 : (p3 → ((p4 ∨ ((True ∧ (p5 ∧ (((False → (p3 → p1)) ∧ True) ∨ p4))) → False)) ∨ (((p2 ∧ p5) → ((p3 ∨ p5) ∧ True)) ∧ (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336283262900459505587918343726 : (p1 → (((p2 ∧ (p4 ∧ (((False ∧ p5) ∨ p4) ∨ (p5 → p5)))) ∨ ((((((p2 ∨ p3) ∨ p5) → p1) ∧ p2) ∧ p4) → (p4 → p2))) ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805945728011602566981235020315 : (((p4 → (((p5 ∧ (((False → (p2 → p2)) → p1) ∧ (((((p1 ∨ p5) ∧ (p5 ∨ p1)) → p2) ∨ p1) ∨ p4))) ∧ (p3 ∧ p3)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637341363811720071540287645996 : (((((p4 ∨ ((((p5 ∧ p3) ∧ True) ∨ (p3 ∨ (p3 ∧ p5))) ∧ p3)) → ((((False ∧ p1) ∨ True) ∨ p3) ∨ (p2 ∨ (p1 → p4)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172012591343847982866977401946 : (((((p1 ∨ ((p5 ∨ False) ∨ p3)) ∨ p4) ∨ (p5 ∨ (p2 → False))) ∨ (True ∨ False)) ∨ (False ∨ ((p5 ∨ (p1 ∨ (p5 ∧ (False → p1)))) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705987034923077519032268601075 : (((((False ∧ p5) ∧ ((True ∨ p4) ∧ (False ∨ p1))) ∧ (((p3 → p5) → ((p1 ∨ (p3 ∧ False)) ∧ ((True ∧ (True → p4)) ∨ p4))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338620487794749611590103046461 : (p1 → ((p4 ∨ (p2 ∨ p4)) → ((False ∨ ((p1 → False) ∧ ((p1 ∨ (False ∧ ((False ∨ (p5 ∧ p1)) ∨ (p1 ∧ (p5 → p3))))) ∨ p2))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h10 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h11 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h12 := h6 h11
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h15 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h1
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h16 := h6 h15
            -- False on the left can always be used.
            apply False.elim h16
          case inr h17 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h18 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h1
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h19 := h6 h18
            -- False on the left can always be used.
            apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h21
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h24 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h25 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h26 := h6 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h29 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h30 := h6 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h32 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h33 := h6 h32
          -- False on the left can always be used.
          apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51520619093913111718928525602 : ((((p1 ∨ p5) ∨ ((True ∨ ((p5 ∨ (False → (p1 → False))) ∧ ((p2 ∨ p2) ∨ p5))) ∨ p1)) → (True ∧ ((False ∨ (True ∨ p3)) ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h19 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229964036027657841879264243304 : (((True ∧ p5) ∧ True) → (((p5 ∧ p4) ∨ (((((p2 ∧ ((((p1 ∧ (p4 → False)) ∧ p2) ∨ True) ∨ p3)) ∧ p3) ∧ p5) ∧ p4) ∨ p5)) ∧ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749841202309318231617983294894 : (((True ∧ ((p3 ∨ (p1 → (p3 ∨ ((p4 ∨ p5) → ((((p5 ∧ p2) ∧ ((p2 → p3) → True)) ∧ (True → (p2 → p4))) ∨ False))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44329901305124658778311972586 : ((((p5 → ((p3 ∧ (p3 ∨ ((True ∨ (p1 ∧ (False → True))) → (p5 → False)))) ∧ p2)) ∨ ((p2 → ((True → False) ∧ p4)) ∨ False)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790639302200277079907302506526 : (((p5 ∨ (p4 ∨ ((((p4 → p4) ∨ p2) ∨ (((((p4 ∧ (False ∨ (True ∨ False))) ∧ (False ∧ p5)) → p1) ∧ False) → (False ∨ p1))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54191399907446739833447606908 : (((((p1 ∨ ((p3 ∨ p2) ∧ p2)) ∧ True) ∨ p1) ∧ (True → (((((p2 ∨ p3) ∨ p4) ∧ True) → (False ∨ p5)) → ((True ∧ True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977218929337533491831521777968 : (((True ∧ (((((p2 ∨ p1) ∧ (True → (p4 ∧ (p5 → p5)))) ∨ True) → (False ∧ p3)) ∧ (((True → (False → p2)) ∨ (p3 ∧ p2)) ∧ p1))) → p4) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (((p2 ∨ p1) ∧ (True → (p4 ∧ (p5 → p5)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : (((p2 ∨ p1) ∧ (True → (p4 ∧ (p5 → p5)))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148893846487449803490691723678 : (((True ∧ (p3 → (True → False))) ∨ (p5 ∧ (p2 → (p2 ∧ ((p4 → (True ∧ (p5 → p5))) ∧ (p5 ∧ True)))))) ∨ ((p5 ∨ (p2 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193164462907834266307443217485 : (((p5 → (True ∧ (p5 ∨ p3))) ∨ ((p3 ∨ p3) → True)) → ((((True ∧ ((True ∨ p2) ∧ p1)) → ((False ∨ True) ∨ p4)) ∧ (p1 ∧ True)) ∨ True)) := by
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
theorem thm_5_vars_725968235397556023271012382944 : (((((p3 → p4) ∧ p4) ∨ ((p3 ∨ (((False ∧ ((((p4 ∨ p2) → (p2 → p4)) → (p5 ∧ True)) → p5)) → True) → (False ∨ False))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230406969412809106866726803512 : (((p4 ∨ True) ∧ p4) → ((p5 ∧ ((((p1 ∧ p4) ∧ False) ∧ ((p2 → (p1 ∧ p1)) ∧ p1)) ∧ True)) ∨ ((p3 ∧ p1) → (True ∨ (p4 ∧ p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252894687697931897798679681953 : ((True ∧ p1) → ((((False ∨ p3) → (p3 ∨ p1)) ∨ ((True → ((p3 → p5) → p1)) ∨ True)) → (((p5 ∨ (p2 → p4)) → p3) ∨ (p1 ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634400385283722999469891415255 : (((((((p4 ∨ p1) ∨ (p5 ∨ (True ∨ (p3 ∨ (False ∨ (False ∧ (p5 ∨ ((True ∧ p5) ∨ p3)))))))) ∨ p4) ∧ ((p1 ∧ p5) → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256991548273381967141336685545 : ((p1 ∨ p5) → (p1 → ((((p3 ∧ p5) ∨ p3) → ((((p4 ∧ p2) ∨ ((p5 → (p1 ∧ True)) ∧ p4)) ∨ True) ∧ (p3 ∧ (False ∧ p3)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40930867185559241892958061282 : (((((p1 ∧ ((((p2 ∧ p5) → p2) ∧ p3) ∨ ((False → (p3 ∧ (p4 → p3))) ∧ ((p4 ∨ p2) ∧ p4)))) ∧ p3) ∨ (p3 → p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690454704608695485429105823296 : ((((((p4 → (p3 ∨ (((p5 ∨ (p1 ∧ p4)) → p5) → p3))) ∨ (p5 ∧ p3)) ∧ p2) → (p1 → ((p2 ∧ (False ∧ p2)) ∧ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308401230719261092964769324609 : (p2 ∨ (((p4 ∨ ((((p4 ∧ False) ∧ (False ∧ ((p5 ∧ True) ∨ ((p4 ∨ p4) → True)))) ∨ (((p5 ∨ p2) → p1) ∨ p5)) ∧ p4)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304092086802843234682594485251 : (p1 ∨ ((True → ((p4 ∨ ((p3 ∧ p5) ∨ (((True → p1) → p1) ∧ ((p5 ∧ (p2 → (p2 ∨ False))) ∨ True)))) ∨ ((p5 → p1) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170263830120666342471763919203 : (((p4 → (p4 → (p5 ∧ (p5 → False)))) → ((p2 → False) ∨ (True ∨ (p1 ∧ p2)))) ∧ (((p5 ∨ (p4 ∧ p1)) ∨ p2) ∨ (p4 ∨ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227369582878113270237794686276 : (((p3 → p5) → p3) ∨ ((p4 ∨ (p3 → (p5 → ((((p3 ∨ (p4 ∧ p1)) ∧ (((p5 ∨ True) ∨ False) ∨ p1)) → True) → False)))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64091870746280845586926770366 : ((False ∨ (((p1 → (p1 ∧ (p4 ∧ p3))) ∧ (((p3 ∨ False) ∨ p1) ∧ p1)) → ((p5 → (p4 ∧ ((True ∨ (p5 → p1)) ∨ p2))) → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197085500504719118026320614498 : (((p1 ∧ ((p3 ∧ p4) ∧ (True ∨ p5))) ∨ p2) ∨ ((p2 ∧ (p4 → ((p4 ∧ p1) ∧ (((p1 → p1) → p4) → (p4 ∨ p2))))) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134963766188755164522327227341 : ((((((p5 ∧ (True ∧ p4)) → (True ∨ p2)) → p5) ∨ ((False ∧ p2) → ((False ∨ p5) ∨ (False → p4)))) ∧ (True ∨ p2)) ∨ (p3 ∧ (p4 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243010243520749544824391802759 : ((p4 → True) ∧ ((True → p1) → ((True ∧ ((True → ((False → p3) → ((((p1 ∧ p3) → False) ∨ (p1 ∧ (True ∧ True))) → False))) → False)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (((p1 ∧ p3) → False) ∨ (p1 ∧ (True ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h9
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225240870977815734112743257997 : (((p5 ∧ p5) ∧ True) ∨ ((((p4 ∧ False) ∧ ((p1 ∧ p4) ∨ (p5 ∧ ((p2 ∨ p1) → p1)))) ∧ ((False → p3) → p4)) ∨ (True ∨ (p4 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254585124156604831669303049483 : ((p3 ∧ p1) → (((p2 ∨ (p3 → ((False → (p2 ∨ (True ∧ (((p5 ∧ (True ∨ True)) → p4) ∨ (p5 ∧ True))))) ∨ p3))) → p5) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616064608868664485462722767474 : (((((p1 ∨ (False → (((p4 → False) ∧ (False ∧ (p2 → (p1 → p3)))) ∨ True))) → ((p2 ∨ p2) ∧ (True ∨ ((False ∨ p4) → False)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_665076067023988117563762920132 : ((((p5 → (((p4 ∨ (p5 → p3)) ∧ (((((p5 ∨ ((p3 ∨ p4) → p1)) → True) ∧ p2) → p2) ∨ (p4 ∧ p4))) → p3)) → (True → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113413104395419189588180929801 : (((((p5 ∨ (((p4 ∨ (p5 ∨ (p5 → True))) ∨ p3) ∨ ((p5 ∨ p5) → (False ∧ (True ∧ p3))))) → p1) ∧ p5) ∨ (True ∨ p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44451397446305515624554256591 : (((((((p3 ∧ (p2 ∨ True)) ∨ p4) ∨ (p1 → p3)) → (p2 ∨ p5)) ∨ (((True ∧ ((p1 ∧ (p2 ∨ p3)) → p5)) ∧ p3) ∨ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136038383932087479889337483936 : (((p3 ∧ (p5 ∧ ((p5 ∨ (True ∨ (p1 → False))) ∨ p1))) → (((p2 ∧ p2) ∨ (p3 → p5)) ∨ ((p2 ∧ True) ∧ True))) ∨ (p4 ∧ (False ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355631259589799219193316098387 : (p5 → ((p4 ∨ (p2 ∨ (p3 → (p3 → (((p1 ∨ p1) ∧ (p1 → ((False ∧ (p5 ∧ (p5 → True))) → p2))) ∨ (p3 → False)))))) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184576441217128100044545038138 : (((True ∧ ((((p2 ∧ p4) → p3) → p1) → p1)) → (False ∧ p4)) ∨ (p1 → ((True → p1) → ((True ∧ p5) → (((p3 ∧ p3) ∨ p1) → p5))))) := by
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199355551859247465973655905267 : (((((False ∨ p1) ∧ p1) ∧ (False ∧ p3)) ∨ p5) → (((((p2 → p3) ∨ (False → ((p1 ∨ p3) ∨ True))) → p2) ∧ p2) ∨ ((False ∧ p1) → p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



