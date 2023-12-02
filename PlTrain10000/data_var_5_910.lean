variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785959240833547688170552908661 : (((p4 ∨ (((((p3 ∨ True) ∧ p1) ∨ ((p2 ∨ p3) ∨ ((p1 → p1) ∨ ((p2 ∧ (True ∧ False)) ∧ p1)))) ∧ (p5 ∧ True)) ∨ (p4 → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299192451972852131632077980428 : (False ∨ (((False ∨ (((p4 ∧ (((p1 → (p3 ∨ True)) ∨ p3) → p5)) → (((p1 ∨ p5) ∧ ((p3 ∨ True) → p5)) → p3)) ∨ False)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191541655723659394371092412804 : ((p1 ∧ ((True → (False → (p1 → (False ∨ p3)))) → p1)) ∨ ((((False ∧ False) → ((p5 ∨ ((p4 ∨ (p4 → p2)) ∨ p2)) ∨ False)) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232422981499118369767510314446 : ((True ∧ (p1 ∧ p1)) → (((((p2 → p3) ∧ p2) ∨ ((False ∨ p2) ∨ ((((p1 → (p3 ∨ p2)) → p1) ∧ (p3 ∨ False)) ∨ False))) ∨ False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192695937640214282992375337959 : ((((p4 → (p4 → (p4 ∨ p5))) ∨ (False → p1)) → False) → ((True ∧ p2) ∨ (((True → ((p3 ∨ True) ∧ (p4 ∨ True))) ∧ p5) ∧ (True ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (p4 → (p4 ∨ p5))) ∨ (False → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153679607902602336267500584307 : ((p2 → ((((p2 ∨ p3) → ((p2 ∨ False) ∨ (True → p5))) ∧ p4) → (((p2 ∧ p2) ∨ p4) ∨ (p5 ∧ p3)))) → ((p5 → (p3 ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148301939706098501575354837436 : ((((p4 → (p4 ∨ p5)) ∧ (((((p5 ∨ p5) → True) ∧ p1) ∧ (False → p2)) → p4)) → ((False ∨ p3) ∧ False)) ∨ (p5 → ((p2 → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47117469853383836072362774828 : (((((p5 ∨ p1) ∨ ((p2 ∧ p3) ∨ ((p4 ∧ ((p3 ∨ (p4 ∨ (p3 ∧ p3))) → True)) → p2))) ∨ (p3 → (p1 ∨ p2))) ∨ (p3 → p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114430058653963502672908695611 : (((p5 ∧ (((p5 ∨ ((p2 ∨ p5) → ((p4 ∨ False) ∨ p5))) → (p4 ∧ (p3 → p1))) ∧ p3)) ∨ ((p3 ∧ (p1 → p2)) ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726544382454856931937061693631 : (((((p5 → False) ∨ p2) ∨ (p3 ∨ ((p4 ∧ ((p1 ∧ p5) → (p4 → (p2 → (True ∧ p5))))) → ((p2 ∨ (True ∧ p2)) ∨ (p4 → True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304681730722036294038847275834 : (p1 ∨ (((p1 ∨ ((p4 ∨ ((p5 ∧ ((p2 → p5) ∨ (((False → ((False ∧ p2) → False)) ∧ p1) → p3))) ∧ p5)) ∨ p5)) ∧ p1) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49013198953792705134171336503 : (((((((p5 → False) → (p2 → ((p2 ∨ (True ∨ p1)) ∧ False))) ∧ (p2 ∨ (p1 ∨ (False ∧ p5)))) → p5) → p2) ∨ (p1 → (p4 → True))) ∨ p2) := by
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
theorem thm_5_vars_354079390541221318122290968699 : (p4 → (p5 → (((((p4 → (p3 ∨ (p1 → (p1 ∧ (p5 ∧ p1))))) → (p5 ∧ ((p4 → False) ∨ p5))) → (True ∨ p1)) → (p1 ∨ False)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_868303845696724424211621378275 : (((((p4 ∨ p3) → (((p1 ∨ p5) → ((True → (p5 ∧ p3)) ∧ ((p2 ∧ False) ∧ p4))) ∨ (p4 ∨ ((p2 ∧ False) → (p1 ∨ p5))))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ p3) → (((p1 ∨ p5) → ((True → (p5 ∧ p3)) ∧ ((p2 ∧ False) ∧ p4))) ∨ (p4 ∨ ((p2 ∧ False) → (p1 ∨ p5))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197770839467798351763028947427 : (((p5 ∨ (False ∧ p5)) ∧ (p1 → (p5 ∧ False))) ∨ (p4 → (False → (((p3 → p2) ∧ ((((p4 → p1) → (False ∧ p5)) ∧ p4) ∧ p1)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40765107783134357414157121837 : (((((p2 ∧ p3) → ((p2 → ((p1 ∧ (((((True ∧ p4) ∧ (True → False)) → p5) ∧ p2) → (p5 ∧ p1))) ∨ False)) → p1)) → p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118102492928247109266987718308 : ((False ∨ ((((((((p5 → p1) ∨ p5) → (True → False)) ∨ (p5 ∧ (p2 → (False ∨ p4)))) ∨ p4) → p1) ∨ (p3 ∧ False)) ∨ True)) ∨ (False → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246530984821165651216904363682 : ((p5 ∧ p1) ∨ ((True → False) ∨ (((True ∨ False) ∧ (((False ∨ p2) ∧ False) ∧ False)) ∨ (True ∧ (False → ((False ∧ (False ∨ (p4 ∧ p1))) ∨ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257784624031068570438597593158 : ((p3 ∨ p4) → (p5 → ((p5 ∧ (p2 ∧ p1)) ∨ (p4 ∨ (((((p1 ∨ p4) → ((p4 → (p2 ∨ p1)) ∧ (p5 → p5))) → p1) → p4) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127767651045753018082845781996 : ((True → ((False ∨ ((p1 ∧ (((False ∧ (p2 ∧ (p3 ∨ (False → True)))) → (False ∨ p5)) ∧ p1)) → p3)) ∧ ((p3 → p1) ∧ False))) → (p2 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639694965236156473306282271869 : (((((p4 ∨ (p3 ∧ True)) ∧ ((p4 ∧ ((p2 → (((p4 → (True ∧ True)) ∧ ((p2 ∧ True) ∧ True)) → p1)) ∧ p2)) ∨ (p3 → p1))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213092849077030508051761800201 : ((((p5 ∧ p5) ∧ True) ∧ False) ∨ (False ∨ (p1 ∨ ((p3 ∧ False) ∨ (((True ∧ ((p3 ∧ True) ∧ (False → (p4 → p4)))) ∧ (p5 → p1)) → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47362931768287888163744365741 : ((((p3 ∨ False) ∨ ((((p2 ∨ (True → (p3 ∧ (p5 ∨ (True ∨ True))))) ∧ (p4 ∧ False)) → (p1 → (p5 ∨ p2))) → p1)) ∨ (p1 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684452781788778246907336245768 : (((((((False → True) → (p1 ∧ (p1 → False))) ∨ False) → (((p3 → p5) ∧ (p3 ∧ False)) ∧ p4)) ∨ ((False → ((p4 ∧ p5) ∧ True)) ∨ False)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48684144162803905622706139093 : ((((p1 → ((p1 ∧ ((True ∧ p1) ∨ p5)) → (p2 → p4))) → (((((p5 → True) → p4) → p1) ∨ p5) ∨ True)) ∧ ((True ∧ p5) → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166684571330178102799746817189 : ((p2 → (((p2 ∨ p1) → p1) ∨ (((False → (p5 → p4)) → p1) ∧ ((p2 ∧ False) ∧ p5)))) ∨ (p1 → ((((p3 → p5) ∧ p4) ∧ False) → p2))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256579771786607291632684684155 : ((p1 ∨ True) → (((False ∨ p3) ∨ (p5 ∨ ((p2 ∨ p3) ∧ ((((p1 ∨ p2) → (p4 ∧ False)) ∨ (((p3 ∧ p1) ∨ True) → p4)) ∧ True)))) ∨ True)) := by
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
theorem thm_5_vars_345355102937423940982355457718 : (p3 → ((((((((p1 ∧ (p1 ∧ (p5 ∧ ((p2 ∧ p1) ∧ p5)))) → (p1 → p4)) → False) ∨ ((p3 → True) → p1)) ∨ False) ∨ p3) ∨ p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699595930727981827674865782254 : ((((((((p2 → p1) ∧ ((True ∧ False) → p4)) → p4) → p2) → True) → ((((p1 → True) ∨ (True ∨ p3)) ∧ (False ∨ (p4 ∨ p2))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112800531802642230835350079054 : (((((((True ∧ p4) ∨ p1) ∨ p5) ∨ p1) ∨ ((True ∨ ((((p1 ∨ False) → p3) ∧ ((p5 → p1) ∨ p4)) → p1)) ∨ False)) → p5) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167306516414897423717835320505 : ((((((True ∨ p4) ∧ p5) ∧ ((p5 ∨ (((p1 ∨ False) ∨ False) ∧ p5)) → False)) → False) → False) → ((p3 → (False ∧ p1)) ∨ (p5 ∧ (p4 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ p4) ∧ p5) ∧ ((p5 ∨ (((p1 ∨ False) ∨ False) ∧ p5)) → False)) → False) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : (p5 ∨ (((p1 ∨ False) ∨ False) ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (p5 ∨ (((p1 ∨ False) ∨ False) ∧ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751654872970672272443355209570 : (((True ∧ (p3 ∧ (((True ∨ p1) → p3) → (((((((p4 → p5) ∨ (p1 → p4)) ∧ p2) → (True → p4)) ∨ (p1 → p3)) → p4) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342190974463328004707091572961 : (p2 → (((((p1 ∧ ((p1 ∧ p5) → (((False → p2) → False) ∧ p5))) → p5) ∧ (p4 ∨ (p3 ∧ p2))) ∨ False) → ((p1 → False) → (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148347659396369188475010866641 : ((((p1 ∧ (p2 ∧ p3)) ∨ ((p2 ∨ p3) ∧ (((True → p5) ∨ False) ∨ p5))) ∧ (((p1 ∧ p4) ∧ p5) ∨ p5)) ∨ (p3 → ((True ∨ p1) ∨ p2))) := by
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
theorem thm_5_vars_191892879205446469344162924055 : ((p5 ∨ ((((p3 ∨ (False ∨ p5)) → p4) → p2) ∨ p5)) ∨ ((True ∧ (True → (p5 ∧ p3))) ∨ (False → ((p1 → ((p3 → p5) ∧ p5)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62399474033699886409340829535 : ((p3 ∧ ((((p3 ∨ p2) ∧ (p3 ∨ (p3 → (p5 → p3)))) ∨ p1) → (p2 → ((p3 → (((False ∨ True) ∨ (p3 → p5)) ∨ p4)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712647707795084984055540769691 : (((((p3 ∧ p2) ∧ (False ∨ (False ∨ False))) ∨ ((p5 ∨ False) → ((False → p3) → (False ∨ ((True ∨ (p3 ∨ ((True ∨ False) ∧ p5))) → p5))))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166470922359469659484890541104 : ((p3 ∨ ((((p5 → p1) → (((p1 → ((p3 ∧ True) → p3)) ∧ p3) ∨ p1)) ∧ p2) ∧ True)) ∨ ((True ∨ ((p5 → p1) ∨ (p5 ∧ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44428555377105427562711994310 : (((((True → ((True → p1) → ((p2 → p1) ∧ (p4 ∨ p5)))) → p2) ∧ ((p2 → False) ∨ (p4 ∨ (((False ∨ p4) → p4) ∧ p3)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777416582296620930885971340878 : (((p1 ∨ (((((p3 ∧ False) ∧ False) ∧ ((p1 ∧ p4) ∨ (True ∨ ((p5 ∧ p1) ∧ p1)))) ∨ True) ∨ (p3 → (p3 ∧ ((p5 → p1) ∧ p2))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190565568373826974617204567590 : (((((p4 ∧ p1) → True) ∧ (False → (p4 ∧ True))) → p5) ∨ (((p2 ∨ ((((p3 ∨ True) ∨ p3) ∧ False) ∧ False)) → True) ∨ (True ∨ (p5 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114740340734606980164376818241 : ((((True ∧ (p5 ∧ False)) → ((True → (p3 → ((True ∧ (True → p5)) → False))) → p3)) → ((p1 ∧ ((p4 ∧ p4) ∨ p5)) ∨ p3)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617315318167308449839108929943 : ((((((p4 ∨ (((p4 ∧ p5) ∨ p4) ∨ p5)) ∨ p4) → (((p3 ∨ (False → (((p2 ∧ True) → p5) ∨ p2))) ∨ p1) ∧ (p3 ∧ p1))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_51268237097294205538773669970 : ((((False → True) → (((p5 ∧ (False ∨ ((p4 ∧ p2) → p2))) ∧ True) ∧ (p4 ∨ (p2 ∧ p3)))) ∨ ((False → True) ∨ ((p2 → p4) ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50442723157349256592644203348 : (((p1 ∨ ((p1 ∨ ((p4 ∧ p4) ∨ ((((((p4 ∧ True) → p2) ∧ p4) → p2) → True) → p2))) ∧ False)) ∨ (((p3 ∨ p1) ∧ p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134612783732744258190971676258 : ((((((False → (((p4 → (p3 → p5)) ∧ p1) ∧ (True → (p5 ∧ False)))) → p5) → True) ∨ (p4 ∨ (p4 ∧ p1))) → p3) ∨ ((False ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151903209835459216732489004349 : ((((p4 ∨ True) → (p2 ∧ ((((p4 ∧ (False ∨ p3)) ∧ p4) ∧ p1) ∧ p3))) → ((p5 ∧ p3) → (p2 ∨ True))) → (p4 → ((p2 ∨ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45961990768420837872589628234 : (((p5 → ((p2 → p2) → ((p2 → ((p3 ∨ p1) ∨ ((False ∧ (p5 ∧ False)) ∨ p1))) ∧ (p5 ∨ (((p3 ∨ p3) ∧ False) ∧ p1))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110761046867068140589628798048 : ((((p1 ∨ (((p2 ∨ False) ∨ (((p4 → False) → p1) ∧ p1)) ∧ (((((False → p3) → False) ∧ p5) ∧ p3) ∨ False))) ∧ p5) ∧ p1) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9815310350472658829148097999 : (((True ∧ ((((p2 ∨ (p4 ∨ p2)) ∨ False) → (p3 → ((False ∨ (p2 → ((p4 ∧ (p2 ∧ p4)) → p1))) ∨ (p3 ∧ p4)))) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204833147930058003512175051352 : ((((p3 ∨ (p5 ∨ p2)) ∨ p2) → False) ∨ (p5 ∨ ((p3 ∧ (((p1 → p2) → (p3 → (p3 ∧ p3))) → p3)) ∨ (p4 ∨ (p4 → (p2 ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66316404760105677284562054348 : ((p5 ∨ (True ∧ ((((p1 ∧ p5) → p3) → ((p5 ∧ p2) ∨ p5)) → (((p2 ∧ False) ∨ (p3 → (p3 ∧ True))) → ((p3 ∨ p5) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116689876376362270720781615244 : (((True ∧ p5) ∨ ((((False ∨ p2) → (True → ((True → (p4 ∧ ((True ∨ (p3 ∧ (p2 → p5))) ∧ p2))) ∨ p5))) ∧ p2) ∧ True)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_886490137222763422092643250449 : (((((((p2 ∨ (p4 ∨ (((((True ∨ p4) → p2) ∨ p1) ∧ p2) ∨ False))) ∧ (((p3 ∨ p4) → p4) ∨ True)) ∨ p2) ∨ True) → (p1 ∧ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ (p4 ∨ (((((True ∨ p4) → p2) ∨ p1) ∧ p2) ∨ False))) ∧ (((p3 ∨ p4) → p4) ∨ True)) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688285377298732703346817287418 : (((((p2 → p1) ∨ (p3 ∨ (p5 ∨ ((p1 ∧ (p5 ∨ p3)) ∨ ((True ∧ p2) ∨ False))))) ∧ ((p1 ∧ (p1 ∨ True)) ∨ ((p3 ∨ p2) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149320239183699068103771873229 : (((p3 ∧ p5) → (p5 → (((p5 ∨ (p5 → p3)) → ((p4 ∨ p2) ∧ False)) ∨ ((p5 ∨ p1) ∨ (p2 → False))))) ∨ (p2 → ((True → p4) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165616587637754031023882809263 : (((p2 → (p2 → ((True ∨ (False ∧ p5)) ∧ p3))) → ((True ∧ (p5 → p4)) ∧ (p5 → p4))) ∨ ((False ∧ ((p3 ∧ (True ∨ False)) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618387055974248938211660599102 : (((((p1 → (p2 ∧ (p5 ∧ True))) ∨ (p3 ∧ ((((p5 → (((p1 ∨ p4) ∧ p2) ∨ False)) ∨ (True ∨ p3)) → False) ∧ (True ∨ p1)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321327991528914987949085494521 : (p4 ∨ (p5 ∨ ((p3 ∧ True) → ((((p4 ∨ (p5 → (p2 ∨ p4))) ∨ (p3 ∧ ((p4 ∨ True) ∧ p3))) ∨ (((p1 ∧ p5) ∨ p5) → p4)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607037070965995406650634728896 : ((((((p1 ∧ ((False ∧ (((True ∨ p4) → (p5 ∨ False)) → p3)) ∨ p5)) ∨ ((p2 ∧ p5) → (((p5 ∧ True) ∨ p4) ∨ False))) ∧ p4) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78743529575983686854982130824 : ((((p2 ∨ ((((p3 → p3) → (p1 ∨ p5)) ∧ p2) → p1)) ∧ ((p4 → p3) ∧ (True ∧ ((p1 ∧ (p3 ∨ p5)) → False)))) ∧ (p4 ∧ p1)) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h23 := h16 h22
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41500039045684642294075169706 : (((((p5 ∨ (p1 ∨ p2)) ∧ (p2 ∨ (False ∧ (False → (p3 → p3))))) → ((True ∨ p2) ∧ ((p2 → ((False ∧ False) ∨ p2)) ∨ p3))) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h30 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h31
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h36 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h37
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- False on the left can always be used.
        apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207018041140504222888920406371 : ((((p1 → True) ∨ (p1 ∨ p1)) ∧ p1) → ((p5 ∧ p4) → ((p5 ∧ (p1 → p3)) → (((p3 ∧ (False ∨ p5)) → ((True ∧ p4) ∧ p2)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (p3 ∧ (False ∨ p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h12
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : (p3 ∧ (False ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h20
        -- One of the premise coincides with the conclusion.
        exact h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h19
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h25 : (p3 ∧ (False ∨ p5)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h26 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h27 := h6 h26
        -- One of the premise coincides with the conclusion.
        exact h27
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h28 := h4 h25
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110894675652737505547045301386 : (((((False → ((p3 → p5) ∨ True)) ∨ ((p4 → (p4 ∨ ((p2 → p2) → (p4 ∨ (p1 → False))))) ∨ (p5 ∧ p3))) → p4) ∧ p2) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254161000477854719256399899093 : ((p2 ∧ p1) → ((p5 ∨ ((True → ((((((p2 ∧ p1) → p1) ∨ p5) → (False → p5)) → (False ∨ p3)) ∨ (p3 ∨ p5))) ∨ p2)) ∨ (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260585147107074316676063001123 : ((p3 → p2) → (((p3 → (((p5 → p1) ∨ (p5 ∧ (True ∨ ((p4 → (p4 → True)) ∨ ((p1 ∨ p1) ∧ (p3 ∧ p5)))))) ∨ p5)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106611103046347358769756650197 : (((p2 ∨ (p5 → ((p2 ∧ True) → (p5 ∧ False)))) → ((p1 ∨ ((p1 ∨ ((p1 → p4) ∨ True)) → (False ∧ p3))) → (p1 ∨ p2))) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∨ ((p1 → p4) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57678694559457808689473109811 : ((((p2 → p2) ∨ p1) → (True → (p1 ∧ ((((((True → p1) ∧ (p1 ∧ p3)) ∧ True) ∧ (p3 → ((True ∧ p4) ∧ False))) ∧ p5) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111448926268890653974502323082 : (((True → ((False ∧ (p5 → ((p1 ∨ ((((p3 ∨ (False → p4)) ∨ (p1 ∨ True)) ∨ p5) ∨ p4)) → p3))) ∨ (p1 ∧ True))) ∧ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469200485050706426222480914716 : (((((p5 ∧ (p1 ∨ (True → False))) → ((((False → p5) → p3) ∧ True) ∨ p5)) → ((p5 ∨ p3) → (((p2 → False) → p1) ∨ (p5 → p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709104646599472442415647188757 : (((((False → (p1 ∧ p1)) ∨ ((p4 → False) ∧ p5)) → (p1 ∨ (p3 ∨ ((((p5 → p4) ∧ p4) ∨ (False ∨ ((p3 ∨ p2) → True))) ∨ p1)))) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56978929348849384048764938143 : (((p4 ∨ (True ∨ True)) ∧ (((False → p2) ∧ True) ∧ (((p3 ∨ p1) ∧ p1) → (((True ∨ (True → p2)) ∧ (p2 ∧ (p4 ∧ p2))) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112320047376055923149099473668 : (((p3 → ((((((p5 ∨ False) → False) ∧ p3) ∧ ((p4 → p2) → (p1 → p5))) → (True → p1)) ∧ ((True ∨ p3) ∧ p2))) ∨ p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265558146930704062146659937492 : (True ∧ (False ∨ (p3 ∨ (((p3 ∧ p5) ∨ ((p3 ∨ ((((True ∧ (p2 → p1)) ∨ (p1 ∨ True)) ∧ True) ∧ (p5 ∨ p1))) ∨ True)) ∨ (p1 ∧ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125535604348852658570054754991 : (((True → p2) ∧ (((p5 ∨ (((True ∨ (p2 ∨ p4)) ∨ ((p5 → p4) ∧ (p4 → (True ∧ True)))) → False)) ∨ (p5 ∧ p3)) → p2)) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56196307369819073822184135897 : (((p5 ∧ (True → (p5 ∨ p2))) ∨ ((p1 → ((False ∨ (False ∨ p3)) ∧ (p1 ∧ p4))) ∨ (p2 ∨ (p2 ∨ ((True ∨ p1) ∧ (p1 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68910908046223328215548899708 : ((p4 → (False ∨ ((p2 → ((True ∧ (True ∨ ((p4 → (True → (p3 ∨ p4))) → p1))) → (((p2 → p3) ∧ p1) ∨ p3))) ∨ (p5 ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_210550722951182185838099793343 : ((((True ∨ p5) ∧ False) → p5) ∧ ((True → (((((p4 ∧ p4) ∧ True) ∧ (p3 ∨ p4)) ∧ (p5 ∨ p1)) ∧ (True ∧ (p5 ∧ p1)))) → (p1 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327877242772212333164624199172 : (True → ((p1 ∧ (p3 ∨ (((((True ∨ p2) ∧ p2) ∧ (p4 ∧ False)) → p4) → ((((p2 ∨ (p1 → True)) → p3) → p5) ∨ True)))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158462767954259299723305857500 : (((p1 → p4) ∨ ((((p4 → ((p2 → False) ∧ True)) ∨ p3) ∧ (p4 ∨ p3)) → ((p4 → p2) ∨ True))) ∨ (((p2 ∨ p4) ∧ p2) ∧ (True → False))) := by
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
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
    cases h3
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
theorem thm_5_vars_789402488780227038597283306323 : (((p5 ∨ (((p4 ∨ p5) ∧ ((((p5 ∨ (p1 ∨ True)) ∨ (True → p4)) ∨ p1) ∨ p5)) ∨ (((p1 → p4) ∧ ((p4 ∧ False) ∧ False)) → p4))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38181563568274410446567174137 : ((((p3 ∧ (p4 ∧ (p2 ∨ ((((False → p1) ∧ ((True → p5) ∨ (False ∨ False))) ∧ p5) ∨ (p2 ∨ p1))))) ∨ ((p1 ∨ True) ∨ p4)) ∧ True) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194065591478653083137533868234 : ((True → ((p3 ∧ (p4 ∧ ((p3 → p5) ∧ False))) ∧ p5)) → (p2 ∧ (p5 ∧ (p3 → (((((p2 → (p5 ∧ True)) → True) ∧ p3) ∧ True) → True))))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218574938728680368901843564422 : (((p1 → p3) → (p3 → False)) → ((True ∨ True) → ((((p3 ∨ (False → (p3 ∨ ((p4 ∧ False) ∨ True)))) → (p4 → (p2 ∨ p3))) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_317803665356278349562518377978 : (p4 ∨ (((p5 ∧ ((p5 → ((p1 ∧ p3) → True)) → p5)) → ((False ∧ p4) ∧ (p3 ∨ ((((p4 ∨ p4) → p3) ∨ (p2 ∧ p5)) ∨ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230973270795544175768679378950 : (((p4 ∧ p2) ∨ p2) → (((((((p3 ∨ True) ∨ False) ∨ p4) ∨ (p4 ∧ p5)) → False) ∧ ((p3 → p2) ∧ p1)) ∨ (p1 → (p1 → (True ∨ p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41284823081729519112202439134 : ((((((p4 ∧ p4) ∧ ((((p1 ∧ p3) → True) → p4) → (p4 ∨ p5))) ∧ ((False ∧ True) ∨ p4)) → (p5 ∧ ((True → p4) → False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118425105351795988274503989403 : ((p2 ∨ (p2 ∨ (((((p2 ∨ (p5 ∧ ((p1 ∨ p4) → True))) ∧ False) ∨ (p3 ∨ ((p3 ∧ p4) → (True → p3)))) ∨ p4) ∨ p2))) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190517175383853530654425901953 : (((((((p5 → False) → p2) ∨ p1) → p4) → p2) → False) ∨ ((((p2 ∨ (p1 ∨ p5)) → p2) → (p4 ∧ True)) ∨ (False → ((p1 ∨ True) ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60425978444413339668010614637 : (((p4 → p3) → (((((p2 ∨ ((False ∨ p2) ∧ ((p1 ∨ p3) ∧ p3))) ∧ p1) ∨ p4) ∧ (True ∧ (p3 → p4))) → (p3 ∨ (False → p4)))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h14.left
        let h18 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h4.left
          let h21 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h4.left
          let h25 := h4.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h4.left
    let h29 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h30
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700325292058836100376222452817 : ((((p2 ∧ (((False → p1) ∨ ((p4 ∧ (True → True)) ∨ True)) ∨ p1)) → (p3 ∨ (((p3 ∨ p1) → (((p1 ∨ p1) → p3) → p5)) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114427532138496553288100573458 : (((p3 ∧ ((p1 ∨ (p5 ∨ ((((p3 ∨ p5) → p3) ∨ False) → (True ∧ (False → True))))) ∧ p5)) ∨ ((False ∨ p2) ∧ (p4 ∧ p3))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41207716805614842593348258055 : ((((p1 → (((False → ((False ∨ p3) ∧ (True ∨ True))) ∧ (p3 ∨ (p3 ∧ (p4 ∧ (p5 ∨ p1))))) → p2)) → (p1 ∧ (True ∧ p1))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116081260750663275843022879701 : ((((p1 ∧ p4) ∨ p4) ∧ (p2 ∧ ((((p4 ∨ (p3 ∨ p2)) ∧ (p1 ∨ p5)) ∧ (p3 → (p1 ∧ p2))) → ((p5 → p1) ∧ False)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149343326464556820944130414780 : (((p2 ∨ False) → ((False ∨ (p3 ∧ (((p3 ∨ ((p4 ∨ False) ∧ p4)) → (p4 → p3)) → p4))) ∧ (False → p1))) ∨ ((p4 ∧ False) → (p5 ∨ False))) := by
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
theorem thm_5_vars_147447158279638756780329656988 : ((((False ∨ p3) ∨ ((((p3 ∨ p3) → (p4 ∧ ((p5 → (p1 → (p1 → p3))) ∧ p2))) ∨ p1) ∧ True)) ∨ p5) ∨ (p1 → ((p5 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354629865772155772808535456748 : (p5 → (((False ∨ ((((p2 ∨ False) ∨ False) ∨ (p2 ∨ False)) ∨ (((p1 → p5) ∧ (p2 ∨ True)) → (p3 ∨ ((p5 ∧ p2) ∧ p4))))) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184627719046431827607125201585 : (((True ∧ (p5 ∨ (False → (p2 ∧ p5)))) ∧ (True → (p5 ∨ p4))) ∨ (p5 ∨ ((((False ∧ p1) ∨ (True ∨ False)) ∨ (True → p2)) ∨ (False ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356660442688884875285362540757 : (p5 → (((p3 ∨ (p4 ∧ p4)) → ((p3 → p2) ∨ p5)) → ((((p3 → p3) ∧ p1) ∧ ((p4 ∧ (True → p4)) → p1)) ∨ ((False ∨ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344359719943814118425772809142 : (p2 → (p4 ∨ ((p3 ∨ ((p1 ∨ (((p3 → (p3 → ((p5 ∧ p4) ∨ p3))) → ((p5 ∨ p5) ∨ (False ∧ p3))) ∧ p4)) ∧ True)) ∨ (p3 ∨ True)))) := by
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



