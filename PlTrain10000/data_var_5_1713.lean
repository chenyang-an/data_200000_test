variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205558404601403976131267713220 : (((p5 ∨ p1) ∧ (p1 ∧ (p2 ∧ p3))) ∨ ((p5 ∧ (((p1 ∨ (True → (p1 → p1))) → p5) → p4)) → (p5 ∨ (p4 ∧ (False ∧ (False ∧ p2)))))) := by
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
theorem thm_5_vars_715662836175382938017662689433 : (((((p3 → (p1 ∨ p3)) ∧ True) ∧ ((p2 ∨ ((p2 ∨ p3) ∨ (((p5 ∨ (p3 ∧ p2)) ∧ (False ∧ p4)) ∧ (p2 ∨ (p1 ∧ p5))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145595776194434343188060060799 : ((((p2 ∧ p1) ∨ p4) → (((((p5 ∨ (p4 → p5)) ∨ p2) ∧ p3) ∨ p3) ∨ (p2 ∨ (p3 → (p3 → p4))))) ∧ ((False → (True ∨ False)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699922824399221964822499396031 : (((((((p3 ∨ True) ∧ False) ∨ (p5 ∨ False)) → ((False ∨ p5) ∧ True)) → (((p4 → (((p1 ∧ p2) ∨ p3) ∧ p2)) → p2) ∨ (False ∨ True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46777395963774879613377539134 : (((p3 → (p3 → ((p1 ∨ p5) ∨ ((p2 ∧ ((True ∨ p2) → (((p4 → (p3 ∧ (False ∧ True))) ∨ p2) → p4))) ∧ False)))) ∧ (p3 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793617840484787108477357780620 : (((True → (p4 ∨ ((((False ∨ p2) ∧ ((p5 ∧ (p4 ∨ (((p3 ∨ (p3 ∧ p1)) ∨ p4) ∨ p3))) ∨ False)) ∧ (True ∧ p3)) ∨ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185017042168307627930753838681 : (((p2 ∨ True) ∧ (((p2 ∨ (True → True)) ∨ p5) ∧ (p1 ∧ p2))) ∨ (False ∨ (p3 ∨ ((p2 → (p4 ∧ ((False → True) ∨ (p5 → p2)))) → True)))) := by
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
theorem thm_5_vars_738013699842953598982751864016 : ((((True ∧ p5) ∨ ((p3 ∧ p4) ∨ (False ∨ (p3 → (True ∧ (p2 ∨ (p5 → (False ∨ ((p5 → p4) ∨ (((p4 ∨ p5) ∧ p4) → p3)))))))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161634366030335540691408502924 : ((False ∨ (False → ((p1 ∨ ((((((p3 → p4) ∨ p4) ∨ False) ∧ p2) → (True ∨ p1)) ∨ p3)) → False))) → ((p4 ∨ (p3 ∨ p2)) ∨ (p4 → p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670532793258852501065302569782 : (((((False ∧ p5) ∨ (((p3 ∧ False) ∧ False) ∨ (((False ∨ p2) → (((p3 ∧ p2) → p5) ∧ (p5 ∧ p3))) ∧ False))) ∨ (False → (p1 → p2))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179167588381908938783831006860 : ((p2 ∧ (p2 ∧ ((p2 ∨ p3) ∨ (((False ∧ (False ∨ p2)) → p1) ∧ p2)))) ∨ (((p4 ∧ p3) → (p5 ∨ p1)) ∨ ((True ∨ p2) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318621403384784773039862230706 : (p4 ∨ (((p5 ∧ p4) ∨ ((((p5 ∨ p1) → (True → p4)) ∨ p1) ∧ ((((p3 ∨ p5) ∨ (p2 ∨ (p3 ∧ False))) ∨ p2) ∧ p4))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40734900264369395678580657711 : ((((((p3 ∧ (p3 ∧ p2)) → p2) → ((True ∨ ((p1 → True) ∧ p3)) ∧ ((((p3 ∨ True) ∨ p1) ∨ p2) ∧ (p2 ∧ p4)))) → p2) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ (p3 ∧ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41430582858891773775834098185 : (((((p1 ∨ ((p4 ∨ p4) → (((p2 ∨ True) ∨ p3) → (True ∧ p2)))) → False) → (False ∨ (((p3 → (p5 → True)) → p1) ∧ p5))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215483310264601146623654450354 : ((p4 ∧ ((p2 ∧ p4) ∧ p4)) ∨ ((p1 → ((p1 ∧ ((p4 ∨ (((True → p5) → p3) → ((p2 → p4) ∨ p1))) ∨ p4)) ∨ (False ∧ True))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147580893826380805481680983184 : ((((False ∨ (p4 ∨ ((True ∧ (((True ∧ p1) ∧ ((p5 → (False ∨ p1)) ∨ p3)) ∨ p4)) → p1))) ∧ p2) → p5) ∨ ((p4 ∧ p1) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_600690438037475015818466714430 : ((((False ∧ (((((((True ∧ False) ∧ ((p5 ∨ (p2 ∨ False)) ∧ p2)) → ((True → p2) ∧ True)) ∨ p5) ∨ p3) → p5) ∨ (p2 → False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806228086534497401511594971876 : (((p4 → (((p1 ∧ ((False ∧ (((p5 ∨ (p4 → p5)) ∧ p2) ∧ (((False ∧ (p2 ∨ p4)) → p1) ∨ p3))) ∧ p3)) ∨ (True ∧ True)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_717896657792871817280551694268 : (((((p2 ∨ (p2 → False)) ∧ p2) ∨ (((p1 ∧ p5) ∨ p5) → (((True → p3) ∨ p4) ∧ (((True ∧ (p3 ∨ (p3 ∨ p1))) ∧ True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228946110307939990268723854931 : ((p4 ∨ (p5 ∨ p5)) ∨ (p4 ∨ (((p1 ∧ p3) ∨ (((p3 ∧ p1) ∧ p3) → p2)) → (p2 → (((p1 → True) ∧ (p5 → p1)) → (p5 ∨ True)))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
theorem thm_5_vars_255869854770579083332931393817 : ((True ∨ p1) → ((((p3 ∧ (p1 ∨ (p3 ∨ (p3 ∧ (False → p5))))) ∧ (False → p2)) → p2) ∨ ((((p1 ∨ (p3 ∧ p1)) ∨ p5) ∨ p1) ∨ True))) := by
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
theorem thm_5_vars_133541587412103973436889377477 : ((((True ∧ (p5 ∧ ((True → (p2 → False)) ∧ ((True ∧ ((p5 ∧ p2) ∨ ((p3 ∨ p5) ∧ True))) ∧ p3)))) ∧ True) ∧ p3) ∨ (True ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679863775462133736967045984403 : (((((p3 → (p4 → ((p4 ∧ True) ∧ ((p5 → (p2 ∧ ((p5 ∧ p4) ∨ (p1 ∧ True)))) → False)))) ∨ p3) → ((p5 ∨ (p2 ∨ True)) ∨ p3)) ∨ p4) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37459674892392922714061860315 : (((((False ∧ (False → (((True → (False → p5)) ∨ p5) ∨ p3))) ∨ ((p1 ∧ ((p4 ∧ p2) ∧ (p1 ∧ (p2 ∧ False)))) ∨ p2)) ∨ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228183178363116900232925849436 : ((p5 ∧ (p3 ∧ p1)) ∨ ((((p5 ∧ False) ∧ ((p2 ∧ p3) ∨ False)) ∧ (((((p4 ∧ (p3 ∧ p4)) → (p5 ∧ p4)) ∨ p2) ∨ True) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175150869696089480991117871305 : ((p5 ∧ (True ∨ ((((p1 → ((p4 → True) ∧ p4)) ∨ (False ∨ True)) ∨ p1) → p3))) → (p2 → (p1 ∨ (((True → p1) → (p4 ∨ p1)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193993165039977908192691302109 : ((p3 ∨ (p3 ∨ ((True ∨ (False ∨ p1)) → (p4 ∧ p3)))) → ((((p5 ∧ (p5 ∧ p4)) → p3) ∧ (p4 ∨ p5)) ∨ (((p1 ∨ p3) → True) ∨ False))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741859194717455450923142443 : (((p5 → ((p4 ∨ True) ∨ p4)) → ((((p5 ∧ p4) ∧ ((p5 ∧ (p1 ∨ (False → p1))) ∧ p2)) ∨ p2) ∨ ((p1 ∧ True) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257272744454788875123946294671 : ((p2 ∨ p3) → ((True ∧ (True ∨ (True ∨ (p1 ∧ True)))) → (((p3 → p2) ∧ ((p1 ∨ p2) ∧ (p4 → (p2 ∧ ((p4 ∧ p3) → p3))))) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h15
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h25
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
        -- Implications on the right can always be decomposed.
        intro h27
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h25
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113443726718817426529889462054 : (((((p1 → False) ∨ ((((p3 ∨ True) ∧ ((False ∨ (((p5 ∨ False) ∨ p2) → p5)) ∨ p4)) ∨ True) ∨ p3)) ∨ p5) ∨ (p2 ∨ p4)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136702379107344833106100735335 : (((p1 ∧ False) ∧ ((p1 ∧ p5) → ((p2 → (p2 → p3)) → ((((p1 ∨ p3) ∨ (False ∨ (True ∧ True))) ∧ True) ∧ p2)))) ∨ (False → (p4 ∧ p5))) := by
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
theorem thm_5_vars_149964084536616326790957970062 : ((p4 ∨ (((p2 ∨ p2) → ((((p1 → p3) ∨ p4) ∧ p2) ∨ (False → (((False ∧ p3) ∧ p2) → p3)))) → p2)) ∨ ((p3 → p1) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49187538096404502847045923034 : ((((True ∨ ((p3 → p5) ∧ p4)) → (((False ∧ p3) ∧ ((((True ∨ p3) ∧ True) → (p3 ∨ p4)) → p5)) ∨ True)) ∨ ((p1 → p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113429604680951724295070948061 : ((((((p4 ∨ ((p1 ∨ False) ∨ (p2 → (((p5 ∨ p5) ∨ p2) ∧ (False ∨ p3))))) ∨ (p1 ∨ p3)) ∧ p5) ∨ p1) ∨ (p4 ∨ p3)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165504356511149030347308944850 : (((p5 → ((((p1 ∧ p3) ∧ True) ∨ p1) ∨ (p3 → p4))) ∨ ((p2 → (p3 → p3)) → p4)) ∨ ((False ∧ (((p2 ∨ p1) ∨ p1) ∨ p4)) → p3)) := by
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
theorem thm_5_vars_259434265371007338326968389313 : ((False → p4) → (((False → p4) → ((p4 ∧ (p5 ∨ ((p2 ∨ p2) → p2))) → (((p2 ∨ True) ∧ p2) → (((p5 → False) ∧ p5) → p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h4.left
  let h9 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h24 := h6 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h26 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h27 := h6 h26
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670540892639141941732689762941 : (((((p2 ∧ p5) ∨ ((((False ∨ p3) ∧ (p5 ∨ False)) ∧ (((p2 → True) ∧ (p4 → (p3 → False))) ∨ p5)) → p1)) ∨ (p2 ∧ (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159956603980585665878905733165 : ((((((p5 ∨ p5) ∧ p5) ∧ (((p1 ∨ p4) → p2) → ((p2 ∧ p1) → p3))) → (p2 ∨ p5)) → p5) → (((p3 ∧ (False ∨ p5)) ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ p5) ∧ p5) ∧ (((p1 ∨ p4) → p2) → ((p2 ∧ p1) → p3))) → (p2 ∨ p5)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48858864027851930744484883559 : (((p3 ∨ (p1 ∨ (False ∨ ((((p4 ∨ p1) → (((False → p3) ∨ False) → False)) ∧ True) ∨ (p2 → (True ∧ True)))))) ∧ (p5 → (True ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729989203875488887786981748216 : (((((True ∨ False) → False) → ((True ∨ (p2 ∧ p4)) → (((p1 ∨ p2) → (p4 ∨ (((p1 ∨ False) ∧ p2) → p2))) ∧ (p4 ∧ (p4 ∨ p5))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h7 := h1 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h24 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h25 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h26 := h1 h25
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199492368382936691240662762019 : (((True → ((p5 → (p4 → p3)) ∧ p3)) ∨ p2) → (p2 → (((((False → p1) ∧ p3) → (p3 ∧ p5)) → (p1 → (p3 → (p1 → p5)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((False → p1) ∧ p3) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : ((False → p1) ∧ p3) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h13
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57418095068251284314666118925 : (((p2 ∨ (p2 ∧ p5)) ∨ ((p5 → ((p2 ∧ ((p5 ∧ (True ∧ (p3 → p2))) ∨ p1)) ∨ ((p1 ∨ p3) ∧ ((True → False) → p3)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328409227059590178797540363427 : (True → ((((p2 → (p1 ∧ True)) → ((p3 ∨ p2) ∧ ((False → p1) → (p2 ∨ (p5 ∨ True))))) → p5) ∨ (p3 ∨ ((True ∨ True) ∨ (p2 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329327824855965885817860753267 : (True → (((p3 ∨ p4) ∧ p3) → ((((p4 → ((p4 ∧ ((p5 ∨ p5) ∧ p4)) → (True ∧ False))) ∨ p1) ∨ True) ∨ (((p4 ∨ p2) → p4) ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56427236456243936899698926303 : ((((p3 ∨ p2) ∧ (p4 ∨ p4)) → (((False ∨ (p4 → ((True ∧ p1) ∨ (False ∨ False)))) ∧ p4) → ((((p4 ∨ p3) ∧ p1) → False) → False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h12 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h13 := h7 h12
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h17 : ((p4 ∨ p3) ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h18 := h3 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- False on the left can always be used.
            apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h23 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h24 := h7 h23
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h28 : ((p4 ∨ p3) ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h29 := h3 h28
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- False on the left can always be used.
            apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h34 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h35 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h36 := h7 h35
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h40 : ((p4 ∨ p3) ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h41 := h3 h40
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- False on the left can always be used.
            apply False.elim h43
          case inr h44 =>
            -- False on the left can always be used.
            apply False.elim h44
      case inr h45 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h46 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h47 := h7 h46
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h48.left
          let h50 := h48.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h51 : ((p4 ∨ p3) ∧ p1) := by
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h45
            -- One of the premise coincides with the conclusion.
            exact h50
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h52 := h3 h51
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h54 =>
            -- False on the left can always be used.
            apply False.elim h54
          case inr h55 =>
            -- False on the left can always be used.
            apply False.elim h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42863469203735982181927329377 : (((p2 → (((False ∨ p2) ∧ True) ∧ ((p3 ∧ (False → ((p3 → True) ∧ p5))) → ((p4 → p5) ∧ (p4 ∧ (p3 ∨ (p4 ∨ p1))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300670331343990068998451554783 : (False ∨ (((((p3 → p5) → ((p1 ∧ True) ∨ (p3 → p4))) ∧ ((p5 → (True ∨ p4)) ∨ p1)) → p2) ∨ (((p3 ∧ p3) → p5) → (False → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317801671396204835441440667385 : (p4 ∨ ((((((p2 → (False → p2)) ∨ p2) → p5) ∨ p2) → (False ∨ (((p3 ∨ True) ∨ (False ∧ (((p2 → False) ∨ p4) ∧ p2))) ∨ p4))) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_205997554269495340320678530219 : ((p1 ∧ (p1 ∨ (True ∧ (p5 → False)))) ∨ ((p4 ∨ ((p5 ∨ p5) ∨ ((((((p4 ∧ p3) → p4) ∨ False) ∨ p2) ∨ p3) ∧ (p4 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319913056507919005376399752570 : (p4 ∨ (((p5 ∧ (p3 ∧ p5)) → False) → (((p2 ∨ ((p3 → p3) → p4)) → ((False ∨ p2) ∨ ((p4 → False) ∨ ((p2 ∨ False) → False)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183794251587580475287014338176 : (((((False ∧ ((False ∧ (True ∧ False)) ∧ False)) ∨ p5) ∨ p1) ∧ p4) ∨ ((False → ((False ∨ (p2 → p2)) ∧ (p1 → ((p3 ∨ False) → p4)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766696171052011486865263991019 : (((p4 ∧ (False ∨ (p2 ∧ (((p1 ∧ (False → (p2 ∨ True))) ∨ (((p1 ∧ (((True → p2) → (p4 → p1)) ∨ p5)) ∨ p1) ∧ p4)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4107310710572944886990527682 : (p3 ∨ (((p1 ∨ (((False ∨ p2) ∨ True) ∨ ((p1 ∨ p1) ∧ p4))) ∨ True) → (((p1 ∨ True) → False) → ((p4 ∨ p5) ∧ (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (p1 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h6 := h2 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h12 : (p1 ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h13 := h2 h12
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h15 : (p1 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h16 := h2 h15
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
  case inr h22 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h23
    -- False on the left can always be used.
    apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250899243755022288257771526134 : ((p1 → p3) ∨ (((p5 → True) ∧ p2) ∨ (True → (((p5 ∨ (p1 → (True → True))) ∧ p1) → (((True → (False ∨ p3)) ∧ (p3 ∨ p2)) ∨ p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736572372809559211588455705640 : ((((p1 → p4) ∧ (((p3 ∧ (p3 ∨ p1)) ∧ ((p5 ∧ ((p3 → p2) ∨ ((False → ((p2 ∨ False) → (p5 → p5))) ∧ p2))) ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778970139345310051565463030238 : (((p1 ∨ (p3 → ((p4 → ((((p5 ∧ False) ∨ (p2 → p4)) → p2) ∨ (((p5 ∨ p2) ∧ ((p2 ∧ (p5 ∨ p1)) → p1)) ∨ p4))) ∨ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326342730259872098086823344785 : (p5 ∨ (p5 → ((((p5 → p1) ∨ p4) → ((((((p3 ∨ p3) ∧ (p5 ∧ (p2 → p5))) ∧ (p4 ∧ p5)) ∨ p2) ∨ True) ∨ (True ∨ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110876117509242573752761428643 : (((((((p1 ∨ ((p5 → ((False → False) ∨ True)) → ((True ∨ (p4 ∧ p5)) ∨ True))) ∧ False) ∧ p5) → (p3 → p2)) → p4) ∧ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303242511335195462488433076131 : (False ∨ (p5 → ((True → (p3 ∧ ((p3 → False) ∧ (False ∧ ((p2 ∧ ((((False ∨ True) ∧ p3) ∧ False) ∨ p4)) ∨ True))))) → ((p4 ∨ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636825618745516079457176638053 : ((((((((p2 ∨ ((p1 ∨ p5) ∨ p4)) → False) → p5) ∧ ((p3 → p5) → True)) → (p2 ∨ (((True ∨ (p3 ∧ p3)) → True) ∨ False))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227255810065132190467176887988 : (((p1 → True) → p1) ∨ ((p2 ∧ p5) → (((p3 ∨ (p2 ∧ (p4 ∨ False))) → p1) → (p3 ∨ (True ∧ (((True → (p1 ∧ False)) ∨ p2) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184512815842121278941100171129 : (((p2 ∧ (((p5 → p4) ∧ (p4 ∧ p4)) → p3)) ∨ (p4 ∨ p3)) ∨ (True ∨ ((p2 ∨ (p1 ∧ p4)) ∧ ((p5 → ((True → p2) → p3)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_385338558665109416659566826965 : (((((p4 → ((p3 ∧ p1) → ((p1 ∧ ((p2 → ((p1 ∨ p1) → True)) ∧ (p4 ∧ ((p3 ∨ p2) ∧ p5)))) → (True ∨ p2)))) → p3) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191049632305684223042141673904 : ((((p1 ∨ p5) ∨ (p1 ∧ False)) → ((p3 → False) ∧ p1)) ∨ ((p5 ∧ ((p2 → (p5 ∧ (p4 → p4))) → (p1 ∧ p3))) → ((True ∨ True) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → (p5 ∧ (p4 → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h6
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (p2 → (p5 ∧ (p4 → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h14
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61104603078355460948343516126 : ((False ∧ ((False ∧ (p5 → ((p3 ∨ (False → p3)) → ((p4 → False) ∧ (p3 → p3))))) ∨ (p3 → (True ∨ ((p3 ∧ False) → (p5 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325624587312952656936030142506 : (p5 ∨ (False ∨ ((p1 ∨ (p5 ∨ (False ∨ ((p3 → False) → (p3 → (p3 ∧ ((False ∨ p3) → ((p1 → p4) → (p1 ∨ p4))))))))) ∨ (True ∧ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198375611289538845532366214796 : ((p3 ∧ (((p5 ∧ p2) → (p3 ∧ p1)) → False)) ∨ (True ∨ ((p1 ∨ ((False ∧ (p3 → (((p2 ∨ (p2 → p1)) ∧ p4) → p1))) ∧ p4)) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617569147885980346747924018436 : (((((p4 ∧ ((p3 ∨ p4) ∧ (p4 → True))) ∧ ((False ∨ (True ∧ p5)) → (p4 ∧ ((p5 → (True ∨ (p4 ∨ p4))) ∧ (p3 ∧ p5))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_157955712740903852916993362472 : (((((False ∨ (p3 ∨ False)) ∨ (p1 ∨ False)) ∨ p2) ∨ ((p2 ∨ ((p1 ∧ (p5 ∨ True)) ∨ p2)) → p3)) ∨ (True ∨ (p5 → (p5 ∨ (True → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147790704612264442909118000061 : (((True ∧ (((True ∧ True) ∧ ((True ∧ (p2 ∨ p4)) → p4)) ∨ (((True ∨ p2) ∨ (p4 ∨ False)) → p4))) → p3) ∨ ((p2 → (True → True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311168824063266795936499611569 : (p2 ∨ ((p5 ∧ p3) → ((p2 ∧ (p4 ∨ (((((p1 ∨ p5) → (p5 ∧ ((p2 → ((p1 ∨ p5) → p1)) ∧ False))) → p4) ∧ p5) → p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_751106790998320853394023937589 : (((True ∧ ((False → ((p3 ∨ p4) ∧ p5)) → ((p2 → (((p4 ∨ p3) ∨ (p1 ∧ p5)) → p1)) ∧ (False ∨ ((p2 → (p5 ∧ p3)) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210102683173485072702551053846 : ((((p3 ∨ p5) ∧ p3) ∨ True) ∧ (((p3 ∨ (True ∨ p4)) → ((((False ∨ True) ∧ (p3 → p3)) ∧ (p4 ∨ p5)) ∧ (p1 ∧ True))) ∨ (False → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340003238380441997217353798102 : (p1 → (p1 → ((False → p3) → (((p4 ∨ p3) → (((p1 ∧ ((p3 ∧ (p5 → (True ∨ True))) → (p4 → (p5 ∧ p4)))) ∨ p3) ∨ True)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255048456319783038397219416243 : ((p4 ∧ p1) → (p1 → (((p2 ∧ ((False ∧ p4) ∧ ((True → False) ∧ (True → p4)))) ∧ False) ∨ (((p2 → (True → (p2 ∧ p5))) → p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52656653033804244057559516156 : (((p2 ∧ ((p2 ∧ (p5 ∨ ((p2 → p4) → True))) ∧ ((p4 ∧ p1) ∧ p5))) ∨ (((p2 ∧ p3) → ((p5 ∧ (p2 ∧ p3)) → p4)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191540428964255375909018798054 : ((p1 ∧ (((p2 ∧ p4) ∨ ((False ∧ p2) → p2)) → p5)) ∨ (((((False ∧ (p4 ∨ p2)) ∨ (True ∨ p4)) ∨ True) ∧ p5) ∨ (True ∧ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301008507944620461296167619780 : (False ∨ ((True → (((((p5 → p1) → (p3 ∧ False)) → p3) ∨ False) → p2)) → (((p1 ∨ (True ∧ (p1 ∨ p5))) ∧ p2) → ((p3 ∨ p1) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200439607376757157719802656070 : (((p4 ∨ p4) ∨ (p4 ∧ (False ∧ (False ∧ p2)))) → ((False ∨ True) → (((True ∨ True) ∧ True) → ((p1 ∧ True) ∨ (p2 ∨ ((p2 → True) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h26
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68352285742254920167595755509 : ((p3 → (((True → p4) ∧ ((True ∨ ((True ∨ True) → p4)) → p1)) → (p5 → ((False → (p3 ∨ (p2 → ((p4 ∨ False) ∨ p5)))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68198166964562051305015912274 : ((p3 → (((p4 ∨ p1) ∨ ((p5 → p1) ∧ (((p5 ∨ ((p5 ∨ p5) ∧ p5)) ∧ (True → (p3 ∨ p3))) → ((True → p4) ∨ p5)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265771020183683419764910272261 : (True ∧ (p4 ∨ (((True ∧ ((True ∧ (p4 → (p4 → True))) ∧ (p3 ∨ p1))) → ((p4 ∧ ((p5 → p4) → True)) ∧ False)) ∨ (True ∨ (False ∧ False))))) := by
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
theorem thm_5_vars_55237018134398885739847636870 : ((((p2 → (p5 → p1)) → (p5 ∨ p3)) ∨ (False → (((p3 ∧ ((((p4 ∧ True) → (p3 → True)) ∨ True) ∧ (p1 ∧ p3))) ∧ p3) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178118257342202531170728968990 : (((((((False ∧ p2) ∧ p2) ∧ False) → p3) ∧ ((True ∧ p5) → p1)) → p3) ∨ ((p4 → (False ∨ (p4 ∨ (((p5 → False) ∧ p3) → p2)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247485954568076791610137483540 : ((False ∨ p3) ∨ (((p1 ∨ ((p1 ∧ (((((p2 ∨ (p1 ∨ p5)) ∧ p2) ∧ p1) ∧ p5) → p1)) ∨ p1)) → p4) ∨ (p5 ∨ ((p5 → p5) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171598318496629273380001929520 : ((((((p1 → p1) ∨ p5) ∧ (p2 ∧ False)) ∧ (True ∨ ((p4 → p1) → p3))) ∨ p2) ∨ ((((p4 → (p1 ∧ True)) → p3) ∨ True) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319029936256621178995015892422 : (p4 ∨ ((((True ∨ (p2 ∨ True)) ∧ ((p4 ∨ ((p2 ∨ ((p1 ∨ p1) → p2)) ∨ p2)) ∨ (p4 → False))) ∨ p1) ∨ (p2 → ((False → p2) ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229908987028933951314796492379 : ((p5 → (p2 → False)) ∨ ((False ∨ (p1 ∧ ((False ∧ (p4 ∨ p3)) → True))) → (p3 → ((p4 → (((True ∧ p2) ∨ p2) ∧ (p1 ∧ p2))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42443742838833217464799666932 : (((p5 ∧ (p1 → ((((((p4 ∨ (((p2 ∨ p4) ∧ (False ∧ p5)) → p5)) ∨ p5) → True) ∧ ((p1 → False) ∨ p5)) ∧ p4) ∧ False))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191650952443986246371421627891 : ((p4 ∧ (False ∧ (((p2 → p5) ∧ False) ∨ (p2 ∨ p1)))) ∨ ((True ∧ (p4 → (((True ∨ p5) ∧ False) ∨ (p2 → (p3 ∨ p5))))) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_64441981469416574127436529961 : ((p1 ∨ ((((p1 ∨ p5) → p3) → (p2 ∧ (((p1 ∧ p1) → False) → (p2 ∧ (False ∨ (((p5 → p3) ∨ p3) ∨ p1)))))) ∨ (p1 → True))) ∨ False) := by
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
theorem thm_5_vars_160315606088065014244126921604 : (((((p2 ∧ (p2 → p5)) ∧ True) ∨ (((False → (p1 ∨ (p5 → p1))) → p4) ∨ p1)) → (True ∧ p1)) → (p5 → ((p4 ∧ (p1 ∧ True)) → p4))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658231542753014699408899656928 : ((((p5 ∧ ((p5 → ((True → ((False ∨ p4) → p5)) ∧ p4)) → ((p4 ∧ (((p4 ∧ p4) ∧ (p4 ∧ p5)) ∧ False)) ∨ True))) ∨ (False ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_43278464110652536750534912551 : (((((((p1 ∨ (((((p5 ∨ False) ∧ (False → p3)) ∧ (p2 ∨ False)) ∧ p5) → (p3 → (p1 ∧ p4)))) → p1) → False) ∧ p2) ∨ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148914367394763987550742619434 : (((((True ∧ p2) ∧ p3) ∨ p2) → ((p5 ∧ (p4 → (p2 → (False → p3)))) ∨ (((p2 → p1) → False) ∨ True))) ∨ ((p1 ∧ (p3 ∧ False)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165668586147752983343613314722 : (((p3 ∨ (p2 ∨ (p2 → (False ∧ p1)))) ∨ ((((p3 ∨ True) ∧ p2) ∨ (True ∧ True)) ∧ p2)) ∨ (((p2 → p2) ∧ (p1 ∧ (p3 ∧ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755840970867892225632027691469 : (((p1 ∧ (((((p4 → (p1 ∧ p1)) → p5) → (p1 ∧ ((((p3 ∨ (((True ∨ False) ∨ p3) → p4)) → True) ∨ p2) ∧ p4))) ∧ p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623785936531394482199065080747 : ((((p1 ∨ (((p1 → p4) ∨ (((True ∨ p1) ∨ p5) → p2)) → (((p1 ∧ p4) → p5) → ((p5 ∨ ((p4 ∧ p2) ∨ p1)) ∧ p2)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_785678921126823711378800593898 : (((p4 ∨ (((((p5 ∨ True) ∧ ((p4 → (p4 → p5)) → p3)) → (p2 → ((p5 ∧ (False ∧ p2)) ∨ (p2 ∨ p5)))) → (p2 ∧ p4)) → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ True) ∧ ((p4 → (p4 → p5)) → p3)) → (p2 → ((p5 ∧ (False ∧ p2)) ∨ (p2 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618897650226018176681272224459 : (((((p1 → (False → p1)) ∧ ((((True ∨ True) → (((True ∨ p4) ∧ (p1 → p2)) ∧ p4)) → (p5 ∨ (True ∧ (p5 → p4)))) ∨ p3)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



