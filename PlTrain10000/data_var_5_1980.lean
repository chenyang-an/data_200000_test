variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225677689563002059696634171746 : (((p2 → p5) ∧ p4) ∨ (((p3 ∧ p2) → ((False ∨ (((p1 ∧ False) ∨ True) → ((False → (p3 ∧ ((True → p5) ∧ p2))) → False))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219983984513852961219700545782 : ((p5 → (p2 ∧ (p1 → p4))) → ((p2 ∨ (p2 ∨ p2)) → ((p2 ∨ False) ∨ (p3 → (((p2 ∧ (p3 ∧ (True ∧ p5))) ∨ (p2 ∨ p2)) → True))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337897669283658678979095955737 : (p1 → (((p3 ∨ True) ∨ (True → (((((p3 → p1) ∨ p4) ∨ p5) ∧ p3) → p2))) → (((p2 → p3) ∨ ((p3 → (p4 → p5)) → p1)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247855006867329246349538387086 : ((p1 ∨ p2) ∨ ((((p4 ∨ p5) ∨ p3) ∨ ((True ∨ (p1 ∧ (False ∨ False))) ∨ False)) ∨ (((False ∨ (((False → p4) ∧ p5) → p3)) ∧ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49075551227763876069567134947 : (((((p1 → (p4 ∨ (p3 → (True ∨ ((((p5 ∨ p1) ∨ p3) → p1) ∨ True))))) ∧ (False → p5)) → (p2 → p3)) ∨ (False → (p5 ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173198233119964569506831235779 : ((p5 ∨ ((((p3 ∧ (True ∧ ((False ∨ (p4 ∨ p1)) → True))) → p5) → p1) ∨ p5)) ∨ ((((p4 → (p3 ∧ p2)) → True) ∨ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354115630582269777431955673599 : (p4 → (p5 → ((p5 → True) → ((((p4 → (p5 ∨ p3)) ∧ (False ∧ ((p5 → (p2 ∨ p1)) ∧ False))) ∧ (False ∧ ((p3 ∨ p5) ∨ p2))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261525166147625958577065352694 : ((p5 → p3) → ((p4 ∨ ((p5 → False) ∨ p2)) ∨ ((((False → (True ∧ (((p3 → p3) ∧ p1) → (True ∧ p4)))) → p3) → p1) → (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False → (True ∧ (((p3 → p3) ∧ p1) → (True ∧ p4)))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89427447237138728452221962773 : (((p5 → (p4 ∧ False)) ∧ ((((p5 ∧ p1) → ((p1 ∧ False) → p2)) → (p5 ∧ p5)) ∧ ((p1 → ((p4 → (p3 ∧ p3)) ∨ p2)) ∨ p2))) → p3) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 ∧ p1) → ((p1 ∧ False) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h7
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h18 : ((p5 ∧ p1) → ((p1 ∧ False) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h22
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h23 := h4 h18
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h25 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h25
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135571031757565170458634578255 : (((((p3 → ((p3 ∨ (p4 ∨ ((False ∧ p4) ∨ (True ∧ p4)))) ∨ p1)) → p3) ∧ p5) ∨ (p3 ∧ ((p3 → p1) ∨ False))) ∨ (False → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179418126137556667361557065257 : ((p4 ∨ ((((p5 ∨ p2) ∨ ((p5 ∨ p1) → p5)) ∧ p1) ∧ (p3 ∧ p4))) ∨ (p1 ∨ ((((p1 ∧ False) ∨ (p3 → False)) ∧ p5) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_185576830337251596902428494701 : ((p5 ∨ ((((p4 → (p1 ∨ p2)) → p2) ∨ (p4 → p3)) ∧ True)) ∨ (((True → True) → (p2 → (p1 → p3))) ∨ ((p1 ∨ p4) → (False → p3)))) := by
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
theorem thm_5_vars_32082014756600923297248069501 : ((p1 ∨ ((p1 ∧ ((((True → p5) ∧ (False ∨ False)) ∧ False) ∧ ((True ∨ ((((p5 ∨ False) → p3) ∨ p1) ∨ True)) ∧ False))) ∨ (True → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_265725131865795002411143779149 : (True ∧ (p3 ∨ (((True → True) → False) ∨ (((p4 ∧ (False ∨ p3)) ∨ (((p4 → p4) → ((True ∧ False) ∨ ((p4 ∧ p2) ∧ p5))) → p4)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_347401008479571181191542093405 : (p3 → (((((p4 ∨ (p4 → p5)) → p2) ∨ True) ∨ False) → (((p5 ∨ ((p3 ∧ p5) → (p2 → ((p4 ∧ p2) ∧ p1)))) ∧ (p4 ∨ False)) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119374044312871284319352001892 : ((p3 → (p4 ∨ (p5 ∧ (p3 ∨ (p2 → (True ∨ ((((p5 ∧ (p5 → p5)) ∧ (False ∨ p3)) ∨ True) → ((p2 ∨ p4) ∧ p2)))))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659221058722018074816130594312 : ((((p4 → ((((p5 ∧ p3) → p2) ∨ (((p1 ∨ ((p3 ∧ (p4 → p1)) ∨ p1)) ∨ p4) → (False → p4))) → (p5 ∧ p2))) ∨ (p3 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_328101599800359820069930073191 : (True → (((p2 ∨ (p5 ∨ ((((((False ∨ p5) → p3) ∧ (p4 → (p3 ∨ False))) ∨ (False ∧ p1)) ∨ True) ∧ p5))) ∨ p4) ∨ ((p4 ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250738006718902713997512559849 : ((p1 → False) ∨ (p3 → ((p1 ∧ (((True ∧ (p1 ∨ (False ∧ ((((p5 ∨ p3) → (p3 ∨ p5)) ∨ p4) ∧ p2)))) → p2) → (p2 ∧ p1))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224431742283565334854349000274 : ((p1 → (p1 ∨ False)) ∧ (((((p1 ∨ ((True → (p4 → p1)) ∨ False)) → ((p2 ∨ (True ∧ p1)) ∨ p3)) ∨ False) ∧ ((False ∨ True) ∧ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305315614462318878183071284494 : (p1 ∨ ((False ∨ (p1 ∧ (((p1 → p4) ∨ ((((p2 → p4) → p1) → p3) ∨ (False ∧ p3))) ∨ False))) ∨ ((((True ∨ p3) ∨ p2) → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134637707805292863393902469549 : (((((p2 ∨ (p2 ∧ (((p3 ∨ ((True ∨ p4) → p2)) → p3) ∨ p5))) → p3) → (p3 ∨ (True ∧ (False → True)))) → False) ∨ (False → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45325329805199853030991028030 : (((p3 ∧ (((p4 ∧ p5) ∨ (True ∨ (False ∨ False))) ∧ (True → ((p3 ∧ (p3 ∧ p1)) ∨ (((p4 → p3) ∧ (p2 → p3)) ∧ p3))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204320420927921059603461709306 : (((p2 ∧ (p4 ∧ (p4 ∨ p3))) ∧ False) ∨ (((False ∧ ((True → ((p3 → False) ∨ (p1 ∧ p3))) ∨ (p2 → False))) ∨ p2) ∨ (False ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_785716352414443593861129081663 : (((p4 ∨ ((((((p5 ∧ p4) ∨ (p1 ∨ (p3 ∧ (p1 ∧ p4)))) → p4) → p5) → (((p3 → True) → False) ∧ ((p1 ∧ p4) ∧ p2))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_570810502501127207756389691935 : (((p1 → ((((((p2 ∨ p2) ∧ (p2 ∨ p2)) ∧ False) ∨ (p5 → (p3 ∧ p2))) ∧ (p1 ∧ (((p3 → p5) → p4) ∧ (p1 → p4)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341090445693946525431060235169 : (p2 → ((p1 → (p3 ∨ (((False ∧ p5) ∧ ((p5 ∨ True) ∨ p1)) ∨ (p2 ∧ (((p4 → (True ∨ (p5 ∨ (p5 ∨ False)))) → False) ∧ p3))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199694593152650573115844937490 : (((True ∧ (p1 ∨ (True ∧ (p1 ∧ False)))) → p3) → (False ∨ (False ∨ ((((((p4 ∧ p3) ∨ p3) → False) → p1) ∨ (p3 ∧ (False ∨ True))) ∨ True)))) := by
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
theorem thm_5_vars_118427684819793353687782297815 : ((p2 ∨ (p3 ∨ (p1 ∧ ((((((((p4 ∨ p3) → False) → p4) ∨ p4) ∨ p5) ∧ ((True → p3) ∧ (p5 ∨ p1))) ∨ p4) ∨ p3)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343321505209848965127895783894 : (p2 → ((p3 ∨ p2) ∧ ((p2 → (((((((p2 ∨ p4) ∧ p5) ∨ True) ∧ (p2 → p4)) → p3) ∨ False) ∨ p2)) ∨ (p5 ∨ ((True → False) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397147503926762411301665867051 : ((((p1 ∨ ((((p1 ∨ (True ∨ (p4 → ((p4 ∨ p2) ∨ (p2 ∨ p3))))) → True) → (p3 ∧ (((p1 → p5) → p5) → True))) ∨ p2)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_66380705717676526452186584338 : ((p5 ∨ (p3 ∨ (p3 → ((True → ((p3 ∧ (p3 → p3)) ∧ False)) ∨ ((True ∧ False) ∧ (((p5 ∨ (p3 → (False ∧ True))) → p1) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114386517939371418386925143006 : (((((p1 ∧ (p3 ∧ ((False ∨ p1) → ((False ∨ True) ∨ p5)))) ∨ (p3 ∨ p1)) ∨ (p3 ∨ p4)) ∨ (((True ∧ True) ∧ p5) → True)) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256928088348088911556738795236 : ((p1 ∨ p4) → (p4 ∨ (p1 ∧ ((p2 ∨ (((False ∧ True) ∧ (p4 ∧ ((p5 → False) ∧ p5))) ∨ p1)) ∨ ((False → (True ∧ (p2 ∨ p3))) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190798868256789954317482082122 : (((((p5 ∨ p1) → p2) → (False ∧ p1)) ∨ (True ∨ False)) ∨ (p3 → (True ∧ (((p4 ∨ ((p5 ∨ ((p2 ∨ p5) ∨ p1)) ∧ p1)) → p4) → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263241183438724390460363061203 : (True ∧ (((((p4 → True) ∧ (True ∧ p4)) ∧ ((p1 ∨ p3) ∨ p2)) ∧ (((p1 → (p4 ∧ (p5 ∧ True))) → (True ∧ p1)) ∧ p4)) → (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52886853261021119306901973087 : (((p2 ∨ ((((p4 ∨ p4) → ((p5 ∧ p2) → False)) → (p4 → p5)) ∨ p3)) → (((p2 ∧ (p2 ∧ (True ∨ p5))) ∧ (p5 → p1)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203687830112266126808237359266 : ((p4 ∨ (((p2 ∨ p3) ∧ p4) ∨ True)) ∧ (((p3 ∨ (False → (((True → p5) ∨ True) ∨ True))) ∧ ((True ∧ (True ∨ p3)) → (p4 → p4))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201328056875555287548113841150 : ((p5 → (((p4 ∧ p3) ∨ (p4 ∨ p2)) → p5)) → ((p3 ∧ (p1 → (((True → (p5 ∧ p3)) ∨ ((p5 ∧ (p1 ∧ p5)) ∧ p2)) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668776384114207642000664059746 : ((((((((True → ((p2 ∨ (True ∧ (((p2 ∧ p2) → True) → p4))) ∨ p3)) ∧ p5) ∨ p3) ∨ (p4 → p4)) ∨ p2) ∨ (p1 ∨ (p5 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594712662144019427488374520017 : (((((((True → p4) ∧ (p2 ∨ False)) → (((p4 ∧ (p2 → (True ∨ p4))) ∧ True) → p3)) → (((p3 ∨ p3) → (False ∧ True)) ∨ True)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171357766085909066829089254272 : (((((p2 ∨ ((p5 ∨ (p2 ∨ p1)) ∧ p5)) ∨ (p5 ∧ p5)) ∧ (p2 → p5)) ∧ p2) ∨ (((p5 ∨ p5) → ((p2 → (p5 ∧ p2)) → p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177999459770158573051155423426 : (((p1 ∨ ((p3 ∧ ((p5 ∨ p2) ∨ p3)) ∧ (p1 → (p3 ∨ p2)))) ∨ True) ∨ (p1 → ((p3 → (p3 ∨ (p5 ∧ p1))) ∨ ((p1 ∧ p2) ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141736240318709948901874170895 : (((True → False) ∧ ((((p2 ∨ (False ∧ p2)) → p2) ∨ (False → ((p4 → (False ∨ ((True ∨ p5) ∧ p3))) → True))) ∨ p2)) → (False ∨ (p4 ∨ True))) := by
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
theorem thm_5_vars_60543589546929439988919787679 : ((True ∧ ((((True ∧ p1) → p5) ∨ ((((((p5 → (p5 → (p4 ∨ p2))) → p2) → p2) → (p1 ∨ (p2 ∨ False))) ∨ p3) ∨ True)) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197241725191684394302878973742 : (((((False ∨ (p5 ∨ True)) → p4) → True) → False) ∨ ((p1 → (False → p5)) ∧ ((((((p1 ∨ True) ∧ p5) ∨ p3) ∨ True) ∨ (True → p1)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165026381216316404655214183091 : ((((p5 ∨ (False → False)) ∧ ((p1 → ((False ∧ p3) ∧ p3)) → (p4 ∧ (p2 → p5)))) → p3) ∨ (p4 ∨ (p4 ∨ ((p2 ∨ (p4 ∨ False)) → True)))) := by
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
theorem thm_5_vars_357357938604636697033238562528 : (p5 → ((p5 → False) ∨ ((p2 ∨ p2) ∨ (((p2 → ((True ∧ (p4 ∧ ((True ∨ p1) ∨ p2))) ∨ p5)) ∧ (p4 → p2)) ∨ (False → (p5 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656309411778110319540596629526 : ((((((True → ((p3 → (p2 ∨ (True ∧ p3))) → p2)) ∧ (p5 ∨ p2)) ∨ ((p2 ∧ (p1 → ((p2 ∨ p4) ∧ p3))) ∧ False)) ∨ (p5 → p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_157875982419495489996829729141 : (((((p4 → p1) ∧ ((p3 ∧ p1) → p1)) ∧ (False ∨ p2)) ∨ ((True → (True ∧ (p5 ∨ True))) → p3)) ∨ (((True ∨ p4) → (p2 ∧ p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158450394892502041928258190562 : (((p5 ∨ p1) ∨ ((((p1 ∧ (p5 ∨ p4)) → True) → (p2 ∧ (True → p3))) ∨ ((True → p5) → p1))) ∨ (p2 → ((p2 → (True → False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315018814103432009391595559359 : (p3 ∨ ((((p1 ∨ p2) ∧ p1) ∨ ((p5 ∨ p4) ∧ p5)) ∨ (p5 ∨ (p3 ∨ ((True ∧ (p5 ∧ (False → p3))) ∨ (True ∨ ((p4 ∨ p4) ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_339728101849431562672578707485 : (p1 → (p4 ∨ ((p5 → (p4 ∨ ((p1 → (((((p5 ∧ (False ∧ p2)) ∨ (p4 ∨ (p5 → p5))) ∨ True) → (p5 → p1)) → p1)) ∧ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327206185656117084474253137734 : (True → ((True → ((p4 → (p5 ∨ ((True → (False → (p2 → ((p4 ∨ ((p4 → p2) → p5)) ∧ p2)))) ∧ ((p2 ∧ p2) ∨ p5)))) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46232317571179824914059456121 : (((((False ∨ (p2 ∨ ((p1 ∨ ((p5 ∧ p4) → (p1 ∨ (True ∧ (p4 ∨ (False → p2)))))) ∧ p5))) → p5) ∨ (p2 ∨ p4)) ∧ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315752949451936087298481946661 : (p3 ∨ ((p5 → p3) ∨ ((False → p1) → (((p2 ∧ (True ∧ (p2 ∧ p5))) ∨ (p2 ∧ ((p1 ∧ False) ∨ ((False ∨ p1) → p4)))) ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190678211930480985078510694208 : (((p3 → ((True ∨ (False ∧ True)) → (p3 ∨ p4))) → False) ∨ ((p5 → ((p5 → (p3 ∧ (p1 ∨ (False ∨ True)))) → p3)) → (True ∨ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308357128850514862209706684314 : (p2 ∨ (((p2 ∧ ((((((p1 ∧ p5) → p1) ∧ (p4 ∨ ((((p5 ∧ (False ∨ p4)) ∨ False) ∧ p1) ∨ p3))) ∧ p5) ∨ False) ∧ p4)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208938819183520654372637122382 : ((p5 ∧ (p2 → (p3 ∧ (False → p4)))) → (((p2 → (((False ∧ p5) → (p2 → p1)) ∨ p5)) → p2) ∨ (((True ∨ True) ∧ False) → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198721258210403283938421523681 : ((p5 ∨ ((False ∧ p4) ∨ (p3 ∧ (p3 ∨ p5)))) ∨ ((p1 ∨ (p2 ∧ (((False → (p3 ∨ False)) → ((p4 ∧ p2) → p2)) → p3))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246254435801330445373990245855 : ((p4 ∧ p4) ∨ (((((True → ((p1 → (p1 → p1)) ∨ (False ∧ p2))) → False) ∧ (p2 ∨ True)) ∨ ((True ∨ (False ∧ p1)) ∨ (True ∨ p2))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649862238473738072642460299419 : ((((((((((True ∧ p4) ∨ p3) ∨ (((p4 → p2) ∨ (p2 → False)) ∧ False)) ∧ False) ∧ p5) ∨ p3) ∧ (True ∧ (p2 ∨ p2))) ∧ (False → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185606233271948560105457858905 : ((True → (((p1 ∨ (((p2 → p5) ∨ p4) ∨ p2)) ∨ p4) ∧ False)) ∨ (((True ∨ (((p3 ∨ (False ∨ p4)) ∧ p5) ∧ (p1 → p3))) ∨ p5) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4413712694324934248820096718 : (p1 → ((((p2 → p5) ∨ p1) ∧ ((p1 → p1) → p1)) → (p3 → (((False ∧ ((p2 → (True → p4)) ∨ p1)) ∨ True) ∨ (p4 ∧ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215486085874413367450677015076 : ((p4 ∧ ((p1 ∨ True) ∧ p4)) ∨ ((((p1 ∨ False) ∨ True) → ((p4 ∧ ((p5 ∨ ((p5 ∨ True) ∧ (True ∧ p3))) ∧ p4)) → False)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187452928383194147290733072943 : ((True ∨ ((((p3 ∧ True) ∧ (False ∧ True)) ∧ p2) ∧ (p3 ∨ False))) → (((False ∧ (p5 ∨ ((p2 → p4) ∧ True))) ∧ False) ∨ ((p3 ∨ p5) ∨ True))) := by
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
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135826471162770857104266694307 : (((((((p5 ∧ p3) ∨ p3) ∨ (p3 → False)) ∨ p4) → (True → p3)) ∧ (p2 ∧ (p4 ∧ (p2 ∧ ((True ∧ p3) ∨ p5))))) ∨ (True ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348056663662251959284503507902 : (p3 → ((p2 ∨ p1) ∨ (p5 → ((((p1 → True) ∧ ((((p5 ∧ True) ∧ p5) ∧ ((p2 ∨ p4) ∨ p1)) ∨ True)) ∨ ((p4 ∨ p3) ∨ True)) ∨ True)))) := by
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
theorem thm_5_vars_184266373906804982745161968508 : (((((False ∨ False) ∨ ((p2 ∧ p1) → False)) ∨ (p4 → p1)) → False) ∨ (True → ((((p1 ∨ ((False ∧ True) ∨ p1)) ∧ (False ∨ False)) ∧ p5) → False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665655141411194155596490147445 : ((((((True → p4) → ((p3 → False) ∨ (((True ∧ (p5 ∨ False)) ∨ (((False ∧ p4) ∨ p3) → False)) → p2))) ∨ p3) ∧ ((p4 ∧ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135519763829772197973513252120 : ((((p1 ∨ (((p5 ∨ p3) ∧ (True ∧ (p2 ∧ (p3 ∨ (p2 → True))))) ∧ p2)) ∧ False) ∧ ((False → (False ∧ False)) → p3)) ∨ ((False → p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260710248843301035464029604381 : ((p3 → p4) → ((False ∨ ((((True ∨ (p3 → p2)) ∧ (p3 ∨ ((p4 ∧ (((p1 ∧ p5) → p2) → p3)) → p5))) ∨ p4) ∨ (False → p4))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111058420076181181012287178060 : (((((p2 ∧ ((p2 ∧ (((True ∨ p5) → (p5 ∧ p1)) → p4)) ∨ p1)) ∨ p5) ∧ ((False ∧ p4) ∧ (p5 ∧ (p3 ∧ p5)))) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358034892793884119021708317217 : (p5 → (p1 ∨ (((((p3 ∨ ((p3 → True) ∨ (p4 ∧ p4))) ∧ ((False ∨ (p4 ∧ p2)) ∧ p4)) ∨ True) → ((p4 → (True → False)) ∨ True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h5.left
        let h16 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h5.left
        let h25 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856493434082700365504511550340 : ((((((((p3 → p2) → p3) ∨ p5) ∧ ((p4 → (p2 ∨ ((((p3 ∨ True) → (p1 ∨ False)) ∧ p1) → True))) ∧ (p2 ∨ p1))) ∨ True) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 → p2) → p3) ∨ p5) ∧ ((p4 → (p2 ∨ ((((p3 ∨ True) → (p1 ∨ False)) ∧ p1) → True))) ∧ (p2 ∨ p1))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677421842572371276223232706401 : ((((((False ∨ ((((p4 ∧ (p3 ∧ (p1 ∨ (True ∧ p2)))) ∨ (p5 ∨ p5)) ∨ p3) → p3)) → p5) ∨ p5) ∨ ((True ∨ (p4 → True)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_247641048504837290412185501882 : ((False ∨ p5) ∨ (p3 → ((((p2 → p3) ∨ (((p5 ∨ (False → p1)) ∧ True) → False)) ∨ p1) → ((p2 ∨ (True ∨ p4)) ∨ ((p4 ∧ p2) ∨ p1))))) := by
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
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670256005939695826579265490650 : (((((((p4 ∨ p1) → p5) ∨ p4) → (((((p3 → False) ∧ p5) ∧ (p1 ∧ (p5 ∧ True))) ∧ (False → p4)) ∧ p5)) ∨ ((True ∨ p1) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_50479701860504865007144049109 : (((p2 → ((((((p4 → (True → p1)) ∨ p3) → (p1 ∨ p3)) ∧ False) ∧ p1) ∨ ((p3 ∧ True) ∧ p4))) ∨ (False → (p1 ∨ (p3 → True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206132022713263564736707162542 : ((p4 ∧ (p2 ∧ ((False → p3) ∧ p5))) ∨ (((p3 → ((p1 ∨ p1) → p4)) ∨ p4) ∨ ((p1 ∧ p1) → ((False ∨ p2) → ((p5 ∨ p4) → p1))))) := by
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
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234129007788833469721019904030 : ((True → (p3 ∨ p3)) → (p3 ∨ ((p5 ∧ ((((p3 ∨ p5) → (p3 → p1)) ∨ ((p1 ∧ True) ∧ p1)) → p5)) → ((p4 ∧ p5) ∨ (False ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159327874213454107015948259683 : ((p5 → (True ∧ ((p1 ∨ ((p1 ∧ ((p1 ∨ ((True ∧ p3) ∧ (True ∨ True))) ∧ True)) ∨ False)) ∧ p2))) ∨ ((False ∨ p5) ∨ ((p5 ∧ p5) → p5))) := by
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
theorem thm_5_vars_254637760614152563032065828206 : ((p3 ∧ p2) → ((True → (True ∧ (((((((p5 ∧ (p1 → (p3 ∧ (False ∧ (p3 ∨ p2))))) → True) ∧ False) ∧ p4) ∧ p5) ∨ p1) ∨ p4))) ∨ p2)) := by
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
theorem thm_5_vars_245305546969238481302583725647 : ((p2 ∧ p2) ∨ ((((p2 ∨ ((p4 → p2) ∧ p1)) ∨ True) ∧ (p3 → p3)) ∨ (True ∧ ((p4 ∨ False) ∧ (True → (p4 ∧ ((False ∧ True) ∧ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_138043622719752282549806640634 : ((True → ((((p1 ∨ p1) ∨ False) → p2) ∧ (((((p3 ∨ (p5 → False)) → p5) → ((p4 ∨ p3) → p5)) ∧ p2) → False))) ∨ (p3 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197261304228156275162457665382 : ((((p5 → ((p5 ∨ False) → p5)) → p1) → p4) ∨ ((p1 ∧ ((((p2 → (((p3 ∨ p4) ∧ p3) ∧ (p1 ∧ p4))) ∨ p2) ∧ p3) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698275464412705328174493849087 : ((((((((p1 ∧ p3) ∨ (p2 → False)) → False) ∧ False) ∧ (p3 ∧ True)) ∨ ((((((False ∧ p2) → p5) → (p3 ∧ p5)) ∧ False) → p2) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233158422659567555960115706728 : ((p5 ∧ (True ∨ True)) → (((True ∨ p4) ∨ p2) → ((p2 ∨ ((((p2 ∧ (p5 ∨ ((p1 ∨ p5) ∨ p4))) ∧ p3) → (p3 ∨ False)) ∧ p1)) ∨ p5))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201344608525989606409496716522 : ((p5 → (p4 ∧ (False ∧ (p4 ∧ (False ∨ p4))))) → ((((p4 → p4) ∧ (p2 ∧ p4)) ∨ (((p5 → (False ∧ (p3 → p2))) ∨ p1) ∨ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317647746555624701300566313307 : (p4 ∨ (((p4 ∨ (p1 ∨ ((((p1 ∧ ((p3 → (p2 ∨ p4)) ∨ p5)) → (False → p3)) → (p2 ∨ p1)) → (p2 ∨ (False ∧ False))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135232579172618119038169062169 : (((((p5 ∨ True) ∨ (True ∧ p3)) ∧ (((True ∧ (p3 ∧ ((p2 → (p2 → True)) ∨ p5))) ∨ p4) ∧ True)) → (p2 → False)) ∨ (True ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_993854861320817654468297062061 : (((p5 ∧ (((p4 → (((False → (True ∧ p1)) ∨ p4) ∨ p3)) → (p4 ∨ ((p5 → (False ∧ (p2 → p1))) ∧ (p1 ∨ (p3 ∨ p1))))) ∧ p3)) → p4) ∧ True) := by
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
  have h6 : (p4 → (((False → (True ∧ p1)) ∨ p4) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h20 := h11 h19
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h23 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h24 := h11 h23
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- False on the left can always be used.
        apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753742169327205791581464426762 : (((False ∧ ((p3 ∨ (False ∧ (((((p4 ∧ False) → p1) ∨ p4) ∧ p1) → p4))) ∧ (p5 ∨ ((False ∧ ((p3 ∨ (p2 → p3)) → p2)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41382052073990160598765390922 : ((((((((p1 ∨ False) ∨ (False ∨ p2)) ∨ (p4 ∧ (p1 → True))) ∧ p2) ∨ p3) ∧ (((((True ∧ False) → p5) ∨ p1) ∨ p3) ∨ False)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183587540893508011871988797356 : ((True → (p5 → (((p3 ∨ (p4 → p5)) ∧ p5) ∧ (True → True)))) ∧ ((((p2 ∧ (p1 ∨ p3)) ∨ p5) ∨ True) ∨ ((p4 ∨ (False ∧ p4)) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173209983695930448258367207781 : ((p5 ∨ ((p2 → ((False ∧ p5) ∨ True)) ∧ (p3 ∧ (p3 → ((p1 ∧ False) ∨ True))))) ∨ ((True ∨ (p1 ∧ (((p3 ∨ False) → p4) ∨ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694467870718722570169511862463 : (((((p3 ∨ p2) → (p1 → ((((True → True) ∨ (p3 ∨ True)) → True) ∧ False))) ∨ (((p5 ∧ ((p3 ∧ p2) → False)) ∧ False) ∨ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134519809214848668553381794416 : ((((False → ((p2 → True) ∨ (p1 ∧ (((p5 ∧ ((False ∧ (p5 ∨ False)) → False)) ∧ True) → (p4 → False))))) ∨ p4) → p2) ∨ (False → (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653352794926248185468334186601 : ((((p3 → (((((p3 ∧ p1) ∨ ((p4 → p2) ∧ ((False → (p4 → p3)) → p3))) ∨ (p1 → p3)) → False) ∧ (p5 ∨ True))) ∧ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754343141731696436374556578358 : (((False ∧ ((p5 ∨ p1) ∨ ((p5 ∨ (False ∧ p5)) ∧ (((p1 → p2) → (True ∨ (p3 → (p5 ∨ ((p1 → True) → p2))))) → (False → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



