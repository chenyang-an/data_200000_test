variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243774966402495177055524884020 : ((p5 → p5) ∧ (((((False ∨ ((p1 → (((((p1 → p2) ∨ (False ∧ p5)) → p1) ∨ False) ∧ p5)) ∨ p4)) ∨ p3) ∧ p4) ∨ p3) ∨ (False → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111898672175079411534176201357 : ((((((((((p1 ∨ False) → False) ∧ (p2 → p4)) → p5) → p5) ∨ p4) ∧ True) → ((((False ∨ True) → p5) → p3) ∨ p2)) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171934849180491214208240325288 : ((((p1 → ((p1 → (p3 ∨ False)) ∧ (False ∧ (p2 → p5)))) ∨ p4) ∧ (p3 ∧ p2)) ∨ (((p3 → False) → p3) ∨ (p4 → (True ∨ (p4 → False))))) := by
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
theorem thm_5_vars_60860913783497342064116086884 : ((True ∧ (p5 ∨ (((((False ∨ False) → (True ∧ p4)) ∨ p5) ∧ (p3 ∨ (((((p3 → p1) → True) → (p1 ∧ p5)) ∨ p1) ∧ True))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768515024127646567235826066166 : (((p5 ∧ (((p1 ∧ (((False ∧ (p2 ∨ False)) → p5) ∧ ((p2 ∨ p5) ∨ (True → p4)))) ∨ True) → (p4 ∧ ((p5 → (p5 ∨ False)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757668255402474457844742588397 : (((p1 ∧ (p5 ∧ (((False → ((p4 → False) ∨ (False ∧ ((True ∨ (p4 ∨ ((p2 ∨ False) → True))) ∨ ((True → True) ∧ p1))))) ∨ p3) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654847998512933132433319455333 : (((((((((p1 ∧ p5) ∨ p3) ∨ (p5 ∨ (p5 → (p3 ∧ ((True → p1) ∧ False))))) ∨ p2) ∨ ((p5 ∧ p2) ∨ p5)) → p3) ∨ (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177774495643718577985725827274 : (((p1 ∧ (p1 ∧ ((((p3 ∨ False) ∧ True) → (True ∧ p1)) ∧ False))) ∧ p4) ∨ ((((p4 ∨ (True ∨ p3)) → p1) ∨ p1) ∨ ((False ∧ True) → False))) := by
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
theorem thm_5_vars_113447897439102870071030333676 : ((((p3 ∨ (((True ∧ p1) ∧ (p5 ∧ p2)) → (((p4 → (p5 ∨ False)) ∧ (False ∧ (p3 → p4))) ∧ p1))) ∨ p3) ∨ (p3 ∨ p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322512102846959652708264797383 : (p5 ∨ ((False ∧ ((p3 ∨ ((p5 → p3) → (p5 ∨ p2))) ∨ (p4 → ((((True → p3) ∨ (p2 → ((True ∨ False) → True))) ∧ p5) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47596761818536835928030872548 : (((p3 → (((((((p1 → (((p2 ∨ False) → (False ∨ False)) ∧ p4)) ∧ p2) → p3) → p2) ∨ p1) ∨ p3) ∨ (p2 ∧ p5))) ∨ (p5 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689571886493793662957639401493 : ((((((((p3 ∨ p5) ∨ p4) → p3) ∧ p2) ∧ (p3 → ((p2 → p2) ∧ (p2 ∨ False)))) ∨ (p5 ∨ ((False ∧ (p2 ∧ p4)) → (p1 ∧ True)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731939477175131477665714949550 : ((((p5 → (True → True)) → ((p5 ∨ False) ∨ (((((p3 → p3) ∨ (p5 ∧ p5)) → (p3 ∨ p4)) ∧ p2) → (p4 ∨ ((True ∨ p3) → p3))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 → p3) ∨ (p5 ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225669948618618928108751094641 : (((p2 → p4) ∧ p1) ∨ ((((p5 ∨ ((p2 ∨ p3) ∧ False)) → p3) → p1) ∨ ((p3 ∧ p2) → (False → ((p3 → p5) ∨ ((p2 → p3) ∧ p3)))))) := by
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
theorem thm_5_vars_61632466568818065559899472695 : ((p1 ∧ ((p3 ∨ p5) → ((((((p5 ∨ p4) → p1) → p1) ∧ p3) → p2) ∨ (p2 ∧ ((True ∧ ((p3 → p5) ∨ (p2 ∧ p1))) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171390066960876390314309264314 : ((((True → ((p5 ∧ p1) ∨ (p4 ∨ p2))) ∧ (True → (True ∨ (p5 → p4)))) ∧ p2) ∨ (p1 → (p2 ∨ ((p4 ∨ (p3 ∨ (False → True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43473855296124472110137319241 : ((((True ∧ ((True → p5) ∨ (((True → ((p2 → True) ∨ p3)) ∧ (((p5 → p3) ∨ True) ∧ True)) ∨ (True ∧ (p3 ∧ True))))) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115779617307806310009216580067 : (((((p5 ∨ p3) ∨ p1) ∧ p5) ∧ (p2 ∨ ((p2 ∧ (p5 ∨ p5)) → (((p3 → p2) ∧ True) ∨ ((p1 → (True ∨ p4)) ∨ p2))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113987395481657432329592907720 : (((p5 ∨ ((((True ∨ p2) ∧ (False ∨ (p5 → p2))) ∨ p2) ∧ (False ∨ (((False ∧ p1) ∧ p2) ∧ p3)))) ∧ (False → (p3 ∧ p5))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621124401819307410340017534336 : (((((p4 → p3) → ((p5 ∧ (p2 → (((p5 ∧ True) ∧ (p1 ∨ False)) ∨ False))) → (((p2 → p1) → (p4 → (p2 ∧ p4))) ∧ False))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_55462585456118284979852991604 : (((((p3 ∧ True) ∧ p5) ∧ (p4 ∨ p5)) → (((((p5 ∨ p4) → (p2 → p2)) → ((p5 ∨ (p2 ∨ p3)) ∨ p4)) → (p2 ∧ p1)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709365671369738512347465988174 : ((((True ∧ ((p3 ∧ p5) ∨ (p2 → (p4 ∧ True)))) → ((((True ∧ (p3 → True)) ∧ p1) ∨ (((p3 ∨ (False ∨ p4)) → p2) → p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48941690932791148057585943934 : (((((p1 ∧ (p2 ∨ p3)) ∧ ((((p5 → (True → (p3 ∧ (p5 → p1)))) ∨ p3) ∧ (p5 → p3)) → p3)) ∧ False) ∨ (False → (p3 ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171325357172674996553194887804 : ((((((p3 ∨ True) ∧ p1) → (((p5 ∧ (p2 → True)) → p4) → p4)) ∨ False) ∧ False) ∨ ((p1 → False) ∨ (((p2 ∧ p1) → True) ∧ (p2 → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166089428464695308447440425661 : (((p5 ∨ p1) → (True ∧ ((((p1 → (False ∧ p3)) ∧ (p4 ∨ p4)) ∧ (p5 ∧ p3)) → p1))) ∨ (True ∨ (p1 → ((True → p2) ∧ (p4 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19497383920254892867810793940 : ((((((p5 ∨ p3) → (((True ∨ (p1 ∧ p1)) → (p2 ∧ True)) → False)) ∧ p2) ∨ True) ∨ (True → ((((p4 ∨ p4) ∧ True) ∨ p5) ∨ p2))) ∧ True) := by
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
theorem thm_5_vars_111880815210824796210428532137 : (((((True ∧ p1) → (True ∧ (p3 ∧ (((p1 ∨ p4) ∧ False) → ((True → False) ∧ p1))))) → (p1 ∨ (p2 ∧ (p1 ∨ p2)))) ∨ True) ∨ (p1 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324179355620677818105381810407 : (p5 ∨ ((p3 ∧ (p2 → ((False → (p4 ∨ p1)) → (False ∧ p4)))) ∨ (((True ∧ ((p3 ∨ p5) → p2)) → p5) → ((p2 ∨ True) ∨ (p1 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747242747675151225700120117563 : ((((p5 ∨ p2) → (((((False → p1) → ((p1 ∧ True) → p3)) → p5) ∧ (False ∨ (((((False ∧ p5) ∨ p5) ∨ p2) → True) → False))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_701668777473242129488446029269 : (((((True ∨ p2) → (True ∧ ((True ∧ (p3 ∧ p5)) ∨ True))) ∧ (((((p5 → (False ∨ (p3 ∨ p2))) → p4) → (True ∨ True)) → p2) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228203657365267726240674371085 : ((p5 ∧ (True ∨ p5)) ∨ ((False ∨ (True → p3)) → ((False → p2) → (((p2 ∧ (p5 → (p1 ∨ (p3 ∧ (p5 ∨ p3))))) ∨ p2) → (True → p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46895825838941725989080198105 : (((((((p2 ∧ False) ∧ p4) ∨ (((p3 ∧ (p2 → False)) ∧ ((p3 ∧ ((p5 ∧ p4) ∨ p5)) ∨ False)) ∧ p5)) → p2) ∨ p1) ∨ (p1 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176996470246570477383495914320 : (((p1 → p1) → (p1 ∨ ((p2 ∧ p5) ∨ (True ∧ (p2 ∨ (False → p2)))))) ∧ (((p2 ∨ False) ∨ (False ∨ ((True → p5) ∨ (p2 ∨ p1)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216698826696485748884815670101 : ((((False ∧ p1) → p5) ∧ True) → ((p5 ∨ ((p1 → (p3 → p4)) ∧ (((p2 ∨ p2) ∨ False) ∧ (p3 → (p2 ∧ (False → p4)))))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40031517605206071929161194073 : (((((((((p3 ∨ (p2 → (True ∧ True))) ∨ p4) ∧ (p3 ∧ ((p5 ∨ p4) ∨ p2))) → p4) ∨ ((False → p1) → p2)) ∧ True) ∧ p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55084061059946057343132744157 : (((False → (p3 ∨ (True ∨ (False → False)))) ∧ ((p3 ∧ (((((False ∧ True) ∨ False) ∨ (p2 → (True → p3))) ∧ p5) ∨ p3)) ∨ (False → p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233253763605301445585998154074 : ((True ∨ (p2 ∧ True)) → (((((((True ∨ p2) ∨ (p5 → ((p1 ∨ p2) → (p3 → p1)))) ∨ p4) ∧ p3) ∨ False) → (p1 ∨ True)) ∨ (False → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66342629732759516750749942954 : ((p5 ∨ (p4 ∧ ((((((p5 ∨ p4) → (p4 ∨ p2)) → (((p1 → (False ∨ p3)) ∧ p5) ∨ (True ∨ (p2 → p5)))) ∧ p1) ∨ p4) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315120515533489448646759338247 : (p3 ∨ ((((p3 ∧ p5) ∧ p5) ∨ (p5 ∧ p5)) ∨ (p2 ∨ (False ∨ (True ∧ ((p2 ∧ ((((p4 ∧ p2) → p4) ∧ True) → p5)) → (p3 ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825160985597313818933287590881 : (((((p2 ∨ (True ∨ p5)) → ((((((p4 → p4) ∨ p5) ∨ False) ∨ ((False → p1) ∨ (True ∧ (p5 → p4)))) ∧ (p1 ∧ False)) ∧ p4)) ∧ p2) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ (True ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44500488966842101177446035049 : ((((p1 ∧ (p1 ∧ ((False ∧ (True ∨ p1)) ∨ (p1 ∨ p5)))) ∧ ((False → (p3 → p5)) ∧ ((p2 ∨ True) → ((p3 ∧ False) ∧ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204336537422449312760414711809 : (((p5 ∧ ((p5 ∧ p4) ∨ p2)) ∧ False) ∨ (p3 ∨ ((p4 → ((((p1 ∧ (((p1 ∧ p3) → (p4 ∨ p4)) ∧ p1)) ∧ p2) ∧ True) → p1)) ∨ p2))) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42143157963411428904231202938 : ((((p5 ∨ p2) → ((p2 ∨ (((p4 ∧ True) ∧ p5) ∧ (False → ((p1 ∨ p5) ∧ (((p2 ∧ (p4 ∧ False)) → p2) → p5))))) → p2)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263989046224650479459776757591 : (True ∧ ((True ∧ ((False ∨ p3) ∨ ((p1 ∧ p5) ∧ ((p5 → p1) ∨ p1)))) ∨ ((False ∧ p5) → ((p4 ∨ p5) → (p2 ∨ ((p5 ∨ p3) ∨ p1)))))) := by
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860144436670311017393177824402 : ((((((p3 → (p3 → False)) → (((True ∧ p2) → ((p4 ∧ p4) ∧ (p1 → (False → ((p4 → p2) ∧ p4))))) ∨ True)) ∨ (p3 ∧ p2)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → (p3 → False)) → (((True ∧ p2) → ((p4 ∧ p4) ∧ (p1 → (False → ((p4 → p2) ∧ p4))))) ∨ True)) ∨ (p3 ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350265532112342978811736660765 : (p4 → ((p3 ∧ (((p3 → (p4 ∨ p4)) → ((p1 → False) ∧ (p4 ∧ ((p1 ∨ ((p5 → (p3 ∨ p3)) → True)) ∧ (p4 ∨ p4))))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147520685068671456895797654985 : (((p5 ∨ ((((False ∨ ((p3 ∨ p5) ∨ (False ∧ (p3 ∨ False)))) ∨ p2) ∨ (p2 ∨ p3)) ∧ (p3 ∨ False))) ∨ True) ∨ (((p4 → p2) → p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111645223563657528498709158292 : ((((((p4 ∨ p2) ∧ p1) ∧ ((((p2 → p4) → (((p4 ∨ False) → (False → (p4 → p3))) → p5)) ∧ p4) ∧ p5)) ∨ p1) ∨ p5) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38298510676529842562652253789 : ((((((p2 ∧ (p5 ∧ (p5 ∨ ((p4 → p4) → p1)))) → (p4 ∨ ((p4 ∨ p5) ∧ p2))) ∧ p4) → (((False ∨ p1) ∧ False) ∧ p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338987729793699459169646729065 : (p1 → ((p5 → p5) → (((False → (((p5 ∧ False) ∨ p3) ∧ False)) ∧ p3) → ((True → ((p5 ∧ p5) ∧ False)) ∨ ((p4 ∨ p3) ∨ (False → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147733501557331819971272059046 : ((((p3 → ((False → (p5 ∧ p1)) ∨ True)) → ((p1 → (False ∧ (p5 ∧ ((p2 ∨ p3) → p5)))) → True)) → p2) ∨ (p3 ∨ ((p5 ∧ p4) → p4))) := by
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
theorem thm_5_vars_49947726998292645849834267215 : (((((p2 → (p4 ∨ (p1 ∧ (p3 ∧ ((p5 → p2) ∧ p3))))) ∧ ((p3 → p4) ∨ p4)) ∨ (p3 ∧ p4)) ∧ ((p3 ∨ p3) ∧ (False → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153197980448071271801114608988 : ((True ∨ ((p1 ∧ (True ∨ (True ∨ ((p3 ∧ ((p2 ∧ ((p3 → False) ∨ p5)) → (p5 → True))) → False)))) ∨ False)) → (False ∨ (False ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198598201128912305578524463078 : ((p2 ∨ ((((True ∧ p4) → True) ∨ False) → False)) ∨ (((True → (p1 ∧ p4)) ∧ (((p1 ∧ p5) ∧ False) ∧ ((True ∧ True) ∧ True))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122442184635361301344060509724 : ((((((p1 → ((p2 ∨ (p3 ∨ True)) ∨ (p1 ∧ p1))) ∨ p3) → p2) → (p3 ∧ ((p5 ∨ (p3 → p4)) ∨ False))) ∨ (True → p2)) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171878446327421123730849354043 : (((p5 ∧ (((p5 ∨ p4) → ((p5 ∧ p3) ∨ (p2 → p1))) ∨ (False → p4))) → False) ∨ (((False ∨ p1) → ((p4 ∨ p4) ∨ p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4252638144472692933862481389 : (p5 ∨ (p4 ∨ ((False ∨ (p1 ∨ (p5 ∨ (True ∧ (p5 → (True → (p4 ∧ p1))))))) ∨ (p4 → ((True ∨ True) ∨ (p1 ∨ (False → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66311849634567608246692246608 : ((p5 ∨ ((p3 → True) → (((False ∧ p5) ∨ (True → ((p5 → (False ∧ (((p1 ∨ (p3 → (False → p2))) → p2) → p4))) → p1))) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172135850131251336123332949575 : ((((p3 ∨ p3) ∨ (p1 → ((p3 → p5) ∨ (False ∧ p1)))) ∧ (False ∧ (p3 ∧ False))) ∨ (True → (True → (False ∨ (True ∨ (False ∨ (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244869334024178560642512987092 : ((p1 ∧ p2) ∨ ((p4 ∨ ((((True → p2) ∨ ((p5 ∧ False) ∧ (((p5 → (p4 ∧ p2)) → (False → False)) → True))) ∨ p3) ∧ True)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60841771971132469457798718557 : ((True ∧ (p1 ∨ (False ∧ (((p1 ∧ p1) → (((p2 ∨ ((p4 ∧ p5) ∨ False)) ∨ (p4 ∧ p3)) ∨ (p4 → True))) ∨ ((p5 → p2) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54768966704152753680190593191 : ((((p4 → False) → (False ∧ (p3 ∧ (p3 ∧ p1)))) → ((p1 ∧ (((p1 ∧ (p1 → p5)) → ((p5 ∨ True) ∧ (p2 → p2))) ∨ p1)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135847881701095815967312549890 : (((True → (p5 → (p2 → ((p1 ∨ ((p1 ∧ True) ∨ True)) ∧ True)))) ∧ (True ∧ ((p1 ∨ ((p3 ∨ p5) → p5)) → p3))) ∨ ((p2 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147094947765517518825939190013 : ((((p5 ∧ (p4 ∧ p3)) ∧ ((p4 → ((True ∧ p3) → p3)) → ((p4 → (p3 ∧ True)) ∧ (p5 ∨ p1)))) ∧ p1) ∨ (False → ((True ∧ p2) → p3))) := by
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
theorem thm_5_vars_64392990748994727739854317005 : ((p1 ∨ ((((p3 ∧ (((p2 → True) ∧ ((p5 ∧ p4) ∨ p5)) ∨ (True ∧ (True ∨ (p1 ∨ (True → (p3 ∧ p5))))))) → p1) → p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48377363710905203039269612891 : (((True → ((((((False → ((p1 ∧ p1) ∨ p2)) ∧ False) ∧ p4) ∨ True) → ((((p3 ∧ p3) ∧ p2) → True) ∧ p2)) ∨ p2)) → (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46489859644579412562243183007 : ((((p3 → (p4 → p5)) ∨ ((p2 → ((p2 → (p2 ∧ p1)) ∨ (((p2 → p2) ∧ p3) ∨ (p2 ∧ p3)))) → (p2 ∧ p5))) ∧ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47069832890314987050818433222 : ((((p3 ∧ (((((((p3 ∨ True) → False) ∨ p1) ∨ p3) → (p2 ∨ (False ∧ p1))) ∨ (True → p5)) ∨ p1)) ∨ (False → p2)) ∨ (True → p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191257452556521980007739805674 : (((p4 ∧ True) ∧ (True ∧ (True ∨ ((p1 ∧ p1) ∨ p5)))) ∨ (p2 → (((p1 → ((p3 → ((p5 → p2) ∧ p1)) → p4)) ∧ p3) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224616162881429500371565437565 : ((p2 → (p5 → p5)) ∧ ((p1 ∨ p1) → (p1 ∧ (False ∨ (p5 → ((p2 ∨ False) ∨ ((p3 ∨ (((p5 ∨ p5) → (p2 → True)) ∨ False)) ∧ p5))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116392376752512130938382537611 : (((p1 ∧ (p2 → p1)) → (p3 → (((((p5 ∧ True) ∨ p5) ∧ p2) ∨ (p2 ∨ ((p5 → False) ∨ p5))) ∧ ((p5 ∨ p1) ∧ True)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103104759416051682435815007976 : (((((p5 ∧ True) → p2) ∨ (p1 ∧ (((((p4 ∨ (True ∨ p1)) → (p3 ∧ p4)) ∨ False) → True) → ((p5 ∧ p5) ∨ False)))) ∨ True) ∧ (False → True)) := by
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
theorem thm_5_vars_42958302780897059604936082375 : (((p5 → ((((p4 ∨ p2) ∨ ((((p1 → (p5 ∧ ((True ∨ p2) ∨ (p2 → p3)))) ∨ (p2 → False)) ∨ p5) → False)) ∧ p5) ∧ p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305699073449310237753231847704 : (p1 ∨ ((((False → ((p2 ∧ p2) ∨ p4)) → (p5 ∨ p5)) ∨ p4) → ((((p3 ∧ p4) → (p1 ∨ p5)) ∨ p4) ∨ ((p2 ∨ p2) ∨ (p5 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False → ((p2 ∧ p2) ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356482473512012171102314321676 : (p5 → ((False ∨ ((((p3 ∧ p1) → p3) ∨ ((True → p5) → p5)) ∨ p4)) → ((((p1 → p4) ∨ (p3 → (p3 → p5))) ∨ False) ∨ (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194182909213931816311130735523 : ((p2 → (False ∧ (True ∨ (((p5 → p5) ∨ p3) ∨ False)))) → (((((p4 → p3) ∨ (False ∧ p4)) ∧ p1) ∨ (p5 → (True ∨ p2))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677339400783088193462338801040 : (((((p5 ∨ ((p1 ∧ ((p2 ∨ ((p5 → p5) ∨ True)) ∨ ((p4 ∨ p5) ∧ True))) ∧ (p1 ∨ False))) ∧ p3) ∨ (p1 → ((False ∨ p3) ∨ p1))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_678035914391305011825247136158 : ((((((p1 → ((p4 ∧ ((p5 → p1) ∨ True)) ∧ (p4 ∧ (False ∨ p5)))) → p2) ∨ (True ∧ (p2 ∨ p1))) ∨ (True ∨ ((p4 ∧ p4) ∧ p4))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_687173967613531687769074276689 : ((((p4 → ((False ∨ (p3 ∧ (((((False → True) ∨ p2) ∨ p4) ∧ p5) → (p3 → p2)))) → False)) → (((p5 ∨ p5) → p1) ∨ (p4 → p4))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119169695103428033240375268174 : ((p2 → (((p5 → p5) → (((((p1 ∨ p3) ∨ p4) ∨ (False ∨ (p1 ∧ p4))) ∨ p4) ∧ (((p4 ∨ True) ∧ p3) ∨ p3))) ∨ True)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654964176634219717438900411825 : (((((((p3 ∨ True) → p3) ∧ (p1 ∨ (((True → False) ∧ p2) → (p4 → (((p2 ∧ p4) → False) ∨ (p3 ∨ p1)))))) → False) ∨ (p4 → True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325805656353526151993957186761 : (p5 ∨ (p3 ∨ ((((((((p3 ∨ p4) → True) ∨ True) → p2) → (p5 → p2)) → (False ∧ (((p2 → p4) ∧ p1) ∨ p2))) ∨ p4) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_313513618499165746456299593444 : (p3 ∨ (((False ∨ ((p5 → (((p4 ∨ p3) → ((p5 → False) ∧ p2)) ∨ ((p1 ∧ (False → p5)) → True))) → (p1 ∧ p5))) ∨ (True ∧ False)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (p5 → (((p4 ∨ p3) → ((p5 → False) ∧ p2)) ∨ ((p1 ∧ (False → p5)) → True))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h5
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179104534474471966802382754831 : ((False ∧ ((p4 ∨ (p4 ∨ p5)) → ((p3 ∧ (True → p2)) ∧ (False ∧ False)))) ∨ ((((False → True) ∨ (False → ((p3 ∨ p4) ∧ p5))) ∨ p1) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53357303101504854616322503695 : (((((p5 ∨ ((p2 ∨ (p1 ∨ True)) ∧ p3)) ∧ (False ∧ p1)) ∨ p2) → (((p1 ∨ p5) → ((p5 ∧ p4) ∧ p1)) → (p3 → (p3 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352400514764998580706184297011 : (p4 → (((True → p4) → False) ∨ (((((p5 ∨ p4) ∨ p3) ∧ ((p2 ∧ p3) ∨ (False ∨ (((p5 ∧ p2) → (False → p3)) ∨ p5)))) ∨ False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216045834082499929017031594055 : ((p5 ∨ (False ∧ (p3 ∨ p2))) ∨ (p3 → ((p4 ∧ p2) ∨ (p2 → (p2 ∧ (((False ∨ p2) ∧ ((((p3 → p4) ∧ False) ∨ p4) ∧ p3)) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124996342621166705773084872316 : ((((p4 ∨ True) ∧ p3) ∧ (p1 ∨ ((True → (p3 ∧ (((p4 ∧ p4) → p1) → ((p2 ∧ ((p1 ∧ p3) ∨ True)) ∨ True)))) ∨ p4))) → (False ∨ p3)) := by
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
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724830950665902950831440959144 : ((((p4 ∨ (p3 ∨ False)) ∧ ((((p3 → p2) → (((p3 ∨ ((p5 → (p3 ∧ p5)) ∨ True)) ∧ p4) ∨ (p2 ∧ (p2 ∧ p4)))) ∧ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183966759723197179531757982239 : (((p2 → ((p1 ∧ (p3 ∨ False)) ∨ (False ∨ (p2 ∧ p1)))) ∧ p1) ∨ (p5 → ((p2 → True) ∨ (((p4 ∧ ((True ∨ p4) → p4)) ∨ p5) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41263976416932183876507099232 : ((((True ∧ ((((p3 ∨ (p3 ∨ p2)) ∨ False) ∨ ((p3 ∧ (False → p4)) ∨ p2)) → (p5 ∧ p3))) ∨ (((False ∨ p3) ∧ p4) ∧ p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45057567389331897239852646221 : ((((p2 → p4) ∨ ((((((((True ∨ p5) → ((p1 ∧ p2) ∧ p5)) → True) ∨ p4) ∨ p5) → p3) → False) ∨ (p2 ∨ (True ∧ p2)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114377710837125030763925554301 : ((((((((p3 ∨ p4) ∨ (p5 ∨ True)) ∧ (False ∧ p1)) ∨ p2) → (False ∨ (False → True))) → p2) ∨ (False → (p5 → (p2 ∨ p5)))) ∨ (p5 ∧ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184842487706704618302338137403 : (((p1 ∨ ((True ∨ True) ∨ p2)) → (p2 ∧ ((p2 → p3) ∧ p2))) ∨ (p4 → (((p4 ∨ ((((p1 ∨ False) ∨ True) ∧ p5) ∨ p1)) ∧ True) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753667220760165266527468923147 : (((False ∧ (((p1 → (True → (p1 ∨ ((p5 ∨ p3) → False)))) → ((p2 ∨ p2) ∧ p4)) ∧ (p4 ∨ (p1 → ((False ∨ (p2 ∧ p5)) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179929512909690259336249594959 : (((((p1 ∨ ((False → p5) → p2)) → (p1 → (p3 → True))) → p5) ∨ True) → (((p3 ∨ p1) → ((False ∨ p3) ∧ ((p5 ∨ p1) → p4))) ∨ True)) := by
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
theorem thm_5_vars_125972271069686119136273688443 : (((p4 ∨ True) → (((False ∧ p2) → (p2 ∨ False)) ∧ ((p1 → p1) → (((False → (((p2 ∧ p4) ∨ p2) → False)) ∨ False) → False)))) → (True → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((False → (((p2 ∧ p4) ∨ p2) → False)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h16 := h8 h9
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218893173457953574431604470751 : ((p3 ∧ ((p3 ∨ p5) ∧ p4)) → ((p5 ∧ ((p5 ∧ (p5 ∨ p2)) ∨ False)) ∨ (p5 → ((True ∧ (p3 ∨ (True ∧ (p2 ∧ (False ∧ p5))))) → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h19
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h19
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147616918282023446264134542558 : ((((p5 → ((((p5 → (p2 ∧ p5)) ∨ (p2 ∧ (p3 ∧ p2))) ∨ ((True ∧ True) → p4)) → p1)) ∨ True) → False) ∨ ((p5 ∧ p4) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51913718494490573194036202404 : ((((p5 ∧ (p3 ∧ (((p3 ∧ p5) ∨ ((p3 ∨ p1) ∧ p2)) ∧ p1))) ∨ (True ∨ p2)) ∨ (((False → (p5 ∧ (True ∨ p5))) ∧ True) ∧ p2)) ∨ p1) := by
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



