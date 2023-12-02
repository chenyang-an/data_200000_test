variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729698394567565156410724457935 : (((((p1 → p5) ∨ True) → ((True ∧ ((((True → p3) → p5) ∨ p4) → p1)) → (((True → p2) ∨ ((p2 → p5) → False)) ∧ (p1 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117680794125475251825216642450 : ((p3 ∧ ((p4 ∧ (p4 ∧ (p3 → (False ∨ False)))) ∨ ((((((True → p1) ∧ p1) ∧ p5) → True) → p5) ∨ ((p3 ∧ True) ∧ False)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690507367870536138050911638408 : ((((((p5 → True) → (p4 → ((p1 → (True ∧ p1)) → ((p4 → p5) → p3)))) ∧ p2) → (True ∧ ((p4 → p5) → (p3 ∨ (p5 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169140256757581709130652366077 : ((p5 → ((p1 → p1) → ((p5 → ((p1 → p5) ∨ (((False ∨ p3) ∨ True) ∧ p4))) ∨ p3))) → (p5 ∨ ((p3 → ((p1 ∧ True) ∨ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150034897824987690046298742262 : ((p5 ∨ (p3 ∧ ((p3 ∨ (((True ∨ (((p3 → False) → p2) ∧ (p4 ∧ (p3 ∧ p2)))) ∨ p1) ∨ p2)) → p5))) ∨ ((p1 → p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669461220560701198584696556521 : (((((p3 → (((p1 ∨ ((p2 → p4) ∨ False)) ∧ (((p4 ∨ (False ∨ p3)) ∧ p4) ∨ p4)) ∧ p1)) ∨ (p1 → False)) ∨ ((True ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206315066413741517576102769617 : ((p1 ∨ ((p5 ∨ p5) → (True ∧ p3))) ∨ ((False ∧ p1) ∨ (((p3 ∨ (p5 ∧ (p5 ∧ (True ∧ p3)))) ∨ False) → ((p4 ∨ True) ∨ (p3 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135350971150606591170534797662 : (((p5 ∧ (((p3 → (p1 ∧ False)) ∨ p3) → ((p5 → (p3 → p4)) ∧ ((p5 ∨ False) ∨ p3)))) ∧ (p2 → (p1 → p5))) ∨ (p4 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248261585085372075904972991790 : ((p2 ∨ p2) ∨ ((p5 → ((p5 → (p4 → True)) ∧ ((True ∧ (p1 ∧ (((p1 → (p4 → (p1 ∨ True))) ∨ p3) ∨ False))) ∨ (p2 ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7790283455901015395898967010 : (((((p1 → ((p2 → False) ∨ (p4 ∧ (False ∧ (p2 → (p4 ∧ True)))))) ∧ ((p5 → p5) ∨ (((p2 ∧ p5) → p3) → True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175436611641400389283689590007 : ((p1 → ((p4 ∨ ((p5 → ((p2 ∨ (p2 → p3)) → p1)) ∨ True)) ∧ (True ∨ p3))) → (p1 ∨ (((p5 ∧ p3) → p2) ∨ (p3 ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259032120938079779987495337914 : ((True → p4) → (((p5 ∧ (p1 → (p1 ∨ (p3 ∨ False)))) ∧ True) → (((p2 → False) ∨ (p5 ∨ ((((p4 → p1) → p1) ∨ p5) → False))) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186564559198846098603283208331 : (((True ∨ (((p4 ∧ p4) ∧ (False → p1)) ∧ p4)) ∨ (p4 ∧ p3)) → (p2 → (((p2 → p3) ∧ (True → ((p4 ∨ p1) ∧ (p3 ∧ False)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62381086983628760000982131069 : ((p3 ∧ (((p1 → (((p2 → p4) → (True → (False ∧ p5))) ∧ (p2 → False))) ∧ True) → (((((p1 ∨ p3) ∨ p4) ∨ True) ∧ p2) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251778931771374557787650380835 : ((p3 → p4) ∨ ((((p5 ∨ ((((p3 ∨ (p3 → ((((False ∧ p2) ∧ p2) ∧ False) ∧ p4))) ∨ p2) ∧ True) ∧ (p5 ∧ False))) ∨ p5) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703069056498377437927872023378 : (((((True ∧ False) ∨ (p2 → (((p1 ∧ p4) ∨ p5) ∨ p1))) ∨ (p4 ∨ (((((p5 ∧ False) ∨ (p3 ∧ p1)) ∨ p4) ∧ False) → (p1 ∨ p4)))) ∨ p4) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319025444716414849526248356879 : (p4 ∨ (((((False → p3) ∧ p4) ∧ ((False → True) → ((p5 ∨ (False ∨ (p5 ∧ p4))) → (p3 ∧ True)))) ∧ p2) ∨ ((True ∨ (False ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258402298429845300706070237338 : ((p5 ∨ p1) → ((p4 ∧ ((((p1 → False) → ((p3 ∧ ((p5 ∧ p4) → p2)) ∨ (p5 ∨ p5))) ∨ (p1 ∧ (p4 ∧ p3))) → (p5 ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_262501412532940624381986629427 : (True ∧ ((p2 → (((p5 ∨ ((p1 → p2) → (p1 ∧ (p5 → False)))) ∨ (p3 ∨ (((p1 ∨ p5) ∨ p2) ∨ p4))) ∧ ((False → p1) ∨ p3))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312930638550779253870878115670 : (p3 ∨ ((p2 → ((p2 → ((p2 ∨ ((p4 ∨ True) ∨ (True ∧ True))) ∧ p5)) → ((p5 ∧ (p1 → (((p1 → p2) → True) → p4))) ∨ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114589688458889751022190728803 : ((((False ∧ p1) ∧ ((p2 ∨ p3) ∧ ((((True ∧ p1) ∨ (p4 → p2)) ∨ p3) → p4))) ∧ ((False ∨ ((p1 ∨ p3) → p4)) ∧ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336157710995427648091765467161 : (p1 → (((((p4 ∨ ((((False → p4) ∧ p5) → ((p3 → p5) → (p3 → True))) ∨ p3)) ∧ (p4 ∨ (p5 ∧ p2))) → (p3 ∧ p1)) → p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349142240537696751813915934582 : (p3 → (True → (p2 → ((((p5 → (p2 ∧ ((p4 → p4) ∧ (p4 ∧ p1)))) ∧ (p3 ∧ p4)) → ((p2 ∨ p3) → p5)) ∨ (p3 ∨ (p2 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51121291286307140583769945455 : ((((((False ∨ p4) ∨ (p5 ∧ ((p3 → p3) ∨ p5))) ∨ ((p2 ∧ (p1 → p1)) ∧ p5)) ∨ True) ∨ ((((True ∧ False) → p2) ∧ p4) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713022658244199064124765692458 : ((((p3 ∧ ((p5 ∨ (p2 ∧ p3)) ∨ p3)) ∨ (True → (True ∨ (p1 → (p5 ∨ (((False → ((True → p5) → True)) → (p3 ∧ False)) ∨ p1)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347187478341372838611784632187 : (p3 → (((((False ∨ (p5 ∨ p5)) ∧ (p2 ∧ p1)) ∨ (True → p5)) ∨ True) ∨ (True ∧ ((False → (((p5 → True) ∧ False) → p4)) → (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184792462533265038486139640114 : ((((p1 → False) ∨ (p5 ∧ p3)) ∨ (((p3 ∨ p4) → True) ∧ p4)) ∨ ((p1 ∧ p4) → (p5 ∨ (((p5 → False) → p4) ∨ (p1 ∨ (p3 ∧ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178610779426746873125063363516 : (((p5 ∨ ((p2 ∧ p1) ∨ (p5 ∨ p5))) ∨ (p3 ∨ ((p2 → True) ∧ True))) ∨ ((p1 → (((p2 ∧ p3) ∧ (True ∧ p2)) ∧ p3)) → (p5 ∨ p2))) := by
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
theorem thm_5_vars_210377233060410689159068600843 : (((True ∨ (p3 → p3)) ∨ p5) ∧ ((True → (((False ∨ p1) ∧ False) ∧ True)) → ((True ∧ (p3 ∨ p5)) ∨ (p1 ∧ ((p5 ∧ (p4 ∧ p1)) ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618123305307287977952994008945 : (((((p4 ∧ (p1 ∧ (p4 → True))) ∧ (((p2 ∧ p4) ∨ False) ∧ (((p4 → p2) → p5) ∨ ((False ∧ ((p5 ∨ p4) ∧ p5)) ∧ p1)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822329158189130540786310259871 : ((((((p4 → True) → ((False → p5) → ((p2 ∧ False) ∧ p1))) ∧ ((p3 ∨ (((p1 ∨ (p2 ∨ (False ∨ True))) ∧ p4) ∨ p4)) ∨ p3)) ∧ p2) → p5) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h8
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (False → p5) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h11
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h21 : (p4 → True) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h23 := h4 h21
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h24 : (False → p5) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- False on the left can always be used.
            apply False.elim h25
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h26 := h23 h24
          -- We need to get the left conjuct of h26 based on <expert-advice>.
          let h27 := h26.left
          -- We need to get the right conjuct of h27 based on <expert-advice>.
          let h28 := h27.right
          -- False on the left can always be used.
          apply False.elim h28
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h31 : (p4 → True) := by
              -- Implications on the right can always be decomposed.
              intro h32
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h33 := h4 h31
            -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
            have h34 : (False → p5) := by
              -- Implications on the right can always be decomposed.
              intro h35
              -- False on the left can always be used.
              apply False.elim h35
            -- We have shown the premise of h33, we can now drive its conclusion.
            let h36 := h33 h34
            -- We need to get the left conjuct of h36 based on <expert-advice>.
            let h37 := h36.left
            -- We need to get the right conjuct of h37 based on <expert-advice>.
            let h38 := h37.right
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h39
            case inl h40 =>
              -- False on the left can always be used.
              apply False.elim h40
            case inr h41 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h42 : (p4 → True) := by
                -- Implications on the right can always be decomposed.
                intro h43
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h44 := h4 h42
              -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
              have h45 : (False → p5) := by
                -- Implications on the right can always be decomposed.
                intro h46
                -- False on the left can always be used.
                apply False.elim h46
              -- We have shown the premise of h44, we can now drive its conclusion.
              let h47 := h44 h45
              -- We need to get the left conjuct of h47 based on <expert-advice>.
              let h48 := h47.left
              -- We need to get the right conjuct of h48 based on <expert-advice>.
              let h49 := h48.right
              -- False on the left can always be used.
              apply False.elim h49
      case inr h50 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h51 : (p4 → True) := by
          -- Implications on the right can always be decomposed.
          intro h52
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h53 := h4 h51
        -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
        have h54 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h55
          -- False on the left can always be used.
          apply False.elim h55
        -- We have shown the premise of h53, we can now drive its conclusion.
        let h56 := h53 h54
        -- We need to get the left conjuct of h56 based on <expert-advice>.
        let h57 := h56.left
        -- We need to get the right conjuct of h57 based on <expert-advice>.
        let h58 := h57.right
        -- False on the left can always be used.
        apply False.elim h58
  case inr h59 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h60 : (p4 → True) := by
      -- Implications on the right can always be decomposed.
      intro h61
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h62 := h4 h60
    -- We want to use the implication h62 based on <expert-advice>. So we show its premise.
    have h63 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h64
      -- False on the left can always be used.
      apply False.elim h64
    -- We have shown the premise of h62, we can now drive its conclusion.
    let h65 := h62 h63
    -- We need to get the left conjuct of h65 based on <expert-advice>.
    let h66 := h65.left
    -- We need to get the right conjuct of h66 based on <expert-advice>.
    let h67 := h66.right
    -- False on the left can always be used.
    apply False.elim h67
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51324009527335968029890657140 : (((True → (p4 ∨ ((p4 → ((p5 → p4) ∨ p4)) → (((p1 → p1) → (p2 → True)) → p4)))) ∨ (p2 → (p1 ∨ (True → (p2 ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113832299295505064787098997159 : (((False ∨ (p5 ∨ ((p4 → p5) → (((False → True) → p4) ∨ (((False → (False ∨ (p4 → p1))) → p4) ∧ p1))))) → (p5 ∨ p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785928071873530893764251308927 : (((p4 ∨ ((p5 ∨ ((False ∧ ((p2 → ((((False → (p5 → False)) ∨ p1) ∧ False) ∧ (p1 → p3))) ∨ (p1 ∧ p2))) ∨ False)) ∧ (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137824275083204311802968440257 : ((p3 ∨ (((p1 ∨ (True ∨ (p3 ∨ True))) ∨ (p1 ∧ ((((p3 → p5) ∨ True) ∨ True) ∨ ((p3 → p2) ∨ p2)))) → False)) ∨ (p1 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204557770457894811579716813628 : ((((p4 → (False ∨ p2)) → p5) ∨ p2) ∨ ((((p5 ∨ ((p2 ∨ p2) → p4)) ∧ False) ∧ (False → (p1 → ((False ∧ p3) → True)))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299368344141001368544843498484 : (False ∨ (((p3 ∧ p1) ∨ ((((((((p2 ∨ p2) → (p4 ∨ (p4 ∨ p4))) ∧ (True ∧ p3)) ∨ (p1 → p2)) ∨ p4) → p2) ∨ False) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144933147457446182008507329431 : (((((True ∧ (p4 ∧ (p2 ∨ ((p5 ∧ (p4 ∧ True)) ∨ p1)))) ∨ p2) ∧ p1) → (False ∨ (p5 ∨ (p3 → p1)))) ∧ (((False ∨ p3) ∨ True) ∨ False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47198253649564256030475891174 : (((((((((p3 ∨ p4) → False) ∨ p2) → (p3 → True)) → p3) → p5) → ((p1 → (((p1 ∨ p1) ∨ True) → p3)) ∧ False)) ∨ (p4 → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115185338065856599012026247407 : (((((p5 ∧ True) → ((False → p2) ∨ p4)) → (p1 → p1)) ∧ ((p3 ∧ (p4 ∨ (True → ((p3 ∧ p1) ∨ (p1 ∧ p4))))) ∨ True)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43499425654823595810603924548 : ((((True ∨ ((p3 ∧ p5) ∧ (((p1 ∧ ((p4 ∨ ((p1 ∨ (p1 ∨ (p4 ∧ p3))) ∨ p1)) ∧ p2)) ∧ p2) ∧ (p2 ∧ p1)))) ∨ True) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118711824699858886588081771573 : ((p5 ∨ (((((p3 ∨ (((p2 ∧ (p1 ∧ False)) ∧ (p5 ∧ (True ∨ p4))) ∧ p1)) ∧ (p3 ∧ True)) ∨ True) ∨ p3) ∧ (False → True))) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41906834870897688983812103679 : (((((p2 ∨ p5) ∨ p3) → (((p4 → False) ∨ (((False ∨ (p4 ∧ (p4 → True))) ∨ p3) ∨ (p5 ∨ p2))) ∨ ((False ∨ p1) ∧ p3))) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244150016924798112203942248678 : ((True ∧ p4) ∨ ((((p3 ∨ p3) ∧ ((p4 → False) ∧ p3)) ∨ ((p3 ∧ p5) → p3)) ∧ (((False → True) ∧ p3) → (((p3 → p3) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191455926727886714758218251758 : (((p3 → True) → (p5 ∨ (p3 → ((p2 ∨ p4) ∨ p5)))) ∨ (p2 → ((True ∨ (False → p3)) ∨ (((((False ∨ p4) ∨ p5) ∨ False) ∨ False) → True)))) := by
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
theorem thm_5_vars_140473762820419767918819649294 : (((p4 → (p1 ∨ (p2 ∧ ((p5 ∨ True) ∧ ((p1 ∧ (p1 ∧ p2)) ∧ ((p3 ∨ p2) → p5)))))) → (p4 → (p4 ∨ True))) → ((True → p4) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358468767117960399207294548244 : (p5 → (p1 → ((p5 → ((((p3 ∧ True) ∨ (p5 → (p4 → (p3 ∧ (p4 ∧ (((True → (False ∧ p5)) → p2) ∨ p3)))))) ∧ False) ∧ p2)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117382904269908753461071848201 : ((p1 ∧ (((((((False → (False ∨ p5)) ∨ False) ∧ (p1 ∧ (p5 → (p1 → (p3 ∧ p5))))) → p5) ∧ p4) ∨ (p5 ∧ p2)) ∧ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316488131354642103223321379946 : (p3 ∨ (p2 ∨ (((((False → p2) → ((((p2 ∧ p2) → (True ∨ p1)) ∧ p4) ∧ (p1 ∧ p1))) ∧ False) ∨ (((True ∧ True) ∨ p1) ∧ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258839890851284792586641363593 : ((True → p1) → (((p4 ∨ ((p5 ∧ (p1 → (((p3 ∧ p4) ∧ ((p2 ∨ p4) ∨ True)) ∨ p3))) ∧ (p5 → p2))) ∧ p4) ∨ ((p4 ∧ p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134362532115897318038990643867 : (((p1 ∨ ((((False → False) ∨ p3) ∧ ((p3 ∨ (p3 ∧ ((p2 → (p1 ∨ p1)) ∧ p3))) → (p1 ∨ False))) → p5)) ∨ p1) ∨ ((p4 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226225556505420285338057171464 : (((p2 ∨ p5) ∨ False) ∨ ((p4 ∨ (p4 ∧ (True ∧ ((p5 ∧ p5) → ((False ∧ ((p4 ∨ (p4 → False)) → p1)) ∨ ((False ∨ p3) → p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88286897156795313882550328415 : (((False → (p1 → (p4 ∧ p2))) ∧ ((((p5 → ((p3 → p4) → ((p4 ∨ p4) ∧ p1))) → (False → p3)) → ((p1 ∨ p3) ∧ False)) ∧ p4)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 → ((p3 → p4) → ((p4 ∨ p4) ∧ p1))) → (False → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41301863896962907199576881861 : ((((p1 → (((p4 ∧ p3) → ((p1 ∧ p3) ∨ ((p5 ∨ False) ∧ ((True → p2) → p2)))) ∧ True)) → (((False ∧ p5) ∧ p4) ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49070273614228974183702017238 : ((((p5 ∨ ((((((p3 ∧ True) ∨ (p1 → (p3 ∧ False))) ∨ (p3 → p3)) ∨ p4) ∨ p1) → p1)) ∨ (p2 ∨ False)) ∨ ((True ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700947878647461156033482658498 : ((((((p1 ∧ False) ∨ (((False → p1) ∨ p3) ∧ p1)) ∨ p1) ∧ (p4 → ((((p3 → (p2 → p2)) ∧ True) ∧ (p3 → True)) ∧ (p4 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61117915420167149269077629375 : ((False ∧ (((p2 ∨ (((p2 ∧ p2) ∧ p1) → (p5 ∨ True))) ∧ False) ∧ ((p1 ∨ (((p3 ∨ False) ∧ True) ∨ (True → p4))) ∨ (p2 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193417831639356968910387098071 : (((p2 ∨ True) ∧ (p1 ∨ ((p2 ∨ (p3 ∧ p4)) → True))) → ((p4 → (p2 → p5)) ∨ (((p4 ∨ ((p3 ∨ p1) ∧ (False → p5))) ∨ True) ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355874867065211221642640668365 : (p5 → (((p2 ∨ p5) → (((True ∨ (p5 → ((p4 ∨ True) → False))) ∧ p1) → ((((p4 ∨ False) ∨ p3) ∨ p3) → False))) ∨ (False → (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47448940305886720958730619472 : (((p3 ∧ (p5 ∨ (((p4 ∧ False) ∨ (p3 ∧ p4)) → (((((p3 ∨ p1) ∧ p3) ∧ True) ∨ False) → ((p1 ∧ p3) ∧ p5))))) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111177978417055691107230344281 : ((((p5 ∨ (p2 → (p5 ∧ p5))) ∨ ((p2 ∧ (((((p2 ∨ (p5 ∨ (p1 ∧ True))) ∨ p3) ∧ p5) ∧ p3) → p4)) → p3)) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219949589184982660388127686728 : ((p5 → ((False ∨ p5) ∧ True)) → (((True ∨ p3) → ((p2 ∨ p4) ∨ ((p4 ∧ (p5 ∧ p4)) ∨ (p2 → (p2 ∨ (p2 ∧ True)))))) ∨ (False ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113803878332158357643767850211 : ((((p3 → p3) → (((p2 ∨ p5) ∨ (p2 → False)) ∧ ((False ∧ ((((p5 → p5) → p1) ∨ True) → p5)) ∨ True))) → (p5 ∨ p5)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178346678691691024534960060432 : (((False ∧ (p5 ∨ (((False → True) ∧ p2) → (p2 ∧ p1)))) ∨ (p3 ∧ False)) ∨ (False → (p5 → (((p1 → ((p3 ∨ p1) → p2)) → p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_814847256654071727983222339356 : ((((((True → (p3 ∨ (False ∧ True))) ∧ (p4 ∨ (p4 → (((p5 ∧ (p1 ∨ p2)) → (p1 ∧ (True ∧ (p2 → p1)))) → p5)))) ∨ p3) ∧ p2) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
  case inr h21 =>
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158316627279540082261992897293 : (((p3 ∨ (p5 ∨ p5)) → (((True ∧ (((p4 ∨ (p5 → p3)) ∧ p1) ∧ p2)) → p2) → (p4 ∨ p3))) ∨ ((p4 ∨ True) ∨ ((p5 ∧ True) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256628179458479472188828431225 : ((p1 ∨ True) → (p2 → ((((p2 → ((p5 ∧ (False ∨ p3)) ∧ p3)) → (p4 ∧ (p5 → p4))) ∨ (p2 ∨ p5)) ∧ (p3 → (True ∧ (p2 ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158330625000011705626751326719 : (((False ∧ True) ∧ (p2 → (((p4 ∨ (p4 ∧ (((p5 ∧ p2) ∨ (p1 → False)) ∨ p5))) ∧ p3) ∧ p2))) ∨ (True ∨ (((p5 ∨ p2) ∨ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185088990309780653065387562991 : (((p3 ∨ p3) ∨ ((p3 ∨ False) ∨ ((p2 ∨ True) → (p3 ∨ True)))) ∨ ((p3 ∨ (((p5 ∨ p1) → (p2 → (p5 → True))) → p5)) ∨ (p4 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_68602328910101121389591193647 : ((p4 → ((((p1 ∧ (p3 ∨ False)) ∨ ((p1 ∧ True) → (((((p5 → p3) → False) ∨ p1) ∨ False) → ((p5 ∨ p3) ∧ p1)))) ∨ p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117737813050708492220992818251 : ((p4 ∧ (((((((p1 ∨ ((p3 → False) ∧ False)) ∧ p5) ∨ False) ∨ p1) ∧ (p4 ∨ (p1 → True))) ∧ ((p2 ∨ p4) ∨ p3)) ∧ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345563442923531305644326387414 : (p3 → ((((p2 ∨ (p5 ∧ p3)) ∨ p5) → ((p4 ∧ (p1 ∧ (p5 ∧ p2))) ∨ (p1 ∨ ((True → (p4 → (False → False))) ∨ (p3 ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594342653220628119765517158249 : ((((((p3 ∧ ((((p5 ∧ False) ∧ True) ∨ p2) → False)) ∨ (p4 ∧ ((p4 → p4) → p4))) ∧ ((False → (False ∧ False)) → (p3 ∧ p4))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148810115626737290279988776001 : (((((p5 → True) ∨ False) ∨ (p3 → p3)) → ((p1 ∧ p1) ∧ (((p1 ∧ (p4 → (False ∧ p3))) → p3) ∧ p3))) ∨ (p2 → ((False → p5) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760427790049651128575835376019 : (((p2 ∧ (True ∧ ((p5 ∨ p1) → (p1 → (((p4 ∨ (((p5 → p1) ∧ (p1 → p3)) → p3)) ∧ p5) ∨ (True ∧ (p4 ∨ (p4 ∨ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342003400720632805582653251837 : (p2 → (((p3 ∧ p2) ∨ ((((p3 ∨ p5) ∨ p1) ∨ (p4 → (p2 ∨ p4))) → (p4 → ((p4 → p3) ∨ (p5 ∨ p4))))) ∨ (p4 ∨ (False ∧ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135033319833346456981785508926 : ((((((False → p4) → ((((p4 → p4) → True) → ((p5 ∨ p2) → False)) → p2)) ∧ (p5 ∨ p5)) ∧ p3) ∨ (True ∨ p5)) ∨ (p1 ∧ (p2 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178671244828048385039578688464 : (((p3 ∧ ((False → p1) ∨ p1)) ∧ (p1 ∨ (False ∧ ((p3 ∨ p4) ∨ p3)))) ∨ (((True ∧ (p1 → p1)) → ((True → p3) ∧ (False → p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141033823548697694291965737874 : ((((False → p2) → ((p4 ∨ (p4 ∧ p3)) ∨ False)) ∧ ((True ∧ ((p3 → True) ∨ (p1 ∨ ((p1 ∨ p1) ∧ p1)))) ∨ p3)) → (p5 ∨ (p4 → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616866406592889582934113359141 : ((((((False ∧ (p4 ∧ (False ∧ (False ∧ (p1 ∧ p2))))) → p5) → (p4 ∧ ((False ∧ ((False ∨ p1) → (p4 ∧ False))) → (p5 → p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652623023130442045089233118356 : ((((False ∨ (False ∨ ((((p5 ∨ False) ∨ (True → p3)) ∧ (((p4 ∧ ((True → True) ∨ p1)) ∧ p2) → p1)) ∨ (p3 ∧ p5)))) ∧ (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315688284176267673814369384077 : (p3 ∨ ((p1 ∨ False) ∨ ((((((p1 → p1) → ((p5 ∨ (False ∧ p4)) ∨ (p5 ∨ (p3 ∧ False)))) → (p4 ∨ p5)) → False) ∧ (p1 ∧ True)) → p2))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 → p1) → ((p5 ∨ (False ∧ p4)) ∨ (p5 ∨ (p3 ∧ False)))) → (p4 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h21 := h2 h6
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49598235355123440850550223650 : (((((p1 ∨ ((p3 → ((p5 ∧ p5) → p2)) ∧ p2)) ∧ p1) ∧ ((p1 ∧ (False ∧ p1)) ∨ ((p5 → p4) ∧ p1))) → ((p4 → p3) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121899598574762319455251540375 : (((p1 ∧ ((True ∨ ((True ∧ (p5 ∧ p2)) ∨ p4)) → (((((p3 ∧ True) ∨ True) ∧ True) ∨ p3) ∧ (p2 ∨ (p1 ∨ True))))) → p4) → (p1 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∧ ((True ∨ ((True ∧ (p5 ∧ p2)) ∨ p4)) → (((((p3 ∧ True) ∨ True) ∧ True) ∨ p3) ∧ (p2 ∨ (p1 ∨ True))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
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
      case inr h12 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_828079797033437878984420793350 : ((((p3 ∧ (((p2 ∨ p3) ∧ (p3 ∨ ((p5 ∧ p4) ∧ (p4 → (p1 → (p3 → (p5 ∧ p5))))))) → (((True ∧ p1) ∧ p2) ∧ False))) ∧ p3) → p4) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∨ p3) ∧ (p3 ∨ ((p5 ∧ p4) ∧ (p4 → (p1 → (p3 → (p5 ∧ p5))))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49575889554677643945513669230 : ((((((p4 → ((p1 → (p5 ∨ p4)) → p1)) ∨ (p3 ∧ p3)) → (p5 ∧ False)) ∨ (((p2 ∧ True) ∧ p1) ∧ True)) → (p4 ∧ (p2 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4387908563367930332402043872 : (p1 → (((((p4 → (p4 → p1)) ∨ p2) ∧ ((p5 → ((p1 → ((True ∨ False) → p1)) → p2)) → (p4 ∨ (p2 ∨ True)))) → False) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51836537989619513972786043657 : (((((p1 ∧ ((((False → (p5 → p2)) ∧ p3) ∧ (p1 ∨ p2)) → False)) ∧ p5) ∧ False) ∨ ((p1 ∧ (p5 ∨ (p1 ∧ (False ∧ True)))) → p1)) ∨ p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47963591788285615198386953505 : ((((((((p1 ∧ p3) → (((p4 ∧ p5) ∧ p1) ∨ p2)) ∨ p3) → p2) ∨ (p1 ∨ p2)) ∧ (False ∨ (p1 ∨ (p1 ∧ p4)))) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92684005932833737252547837118 : (((p2 → True) → ((((False → False) → ((p3 → ((((p5 → p1) ∧ p4) ∧ (p3 ∨ ((True ∧ p4) ∧ p3))) → True)) → p4)) → p4) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51192688387556979100585705148 : (((((True → ((p2 → p4) ∨ ((p4 → (False → p3)) ∧ p1))) → p1) → (p4 → (p3 → p2))) ∨ (p2 → (((p2 → p3) ∨ p4) → p2))) ∨ p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135354420910891060792477523469 : (((p1 ∨ (p5 ∨ (p5 ∨ (p3 ∨ ((p2 ∧ (p2 ∧ (p5 ∨ (p2 ∧ (p5 ∧ p3))))) ∨ p4))))) ∧ ((p4 ∧ p2) → p2)) ∨ ((p5 ∧ p4) → p5)) := by
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
theorem thm_5_vars_797158025787439690297348831791 : (((p1 → ((p5 ∧ ((p2 → ((True → p3) → p5)) ∨ (((((p1 → True) → p2) ∨ p1) ∧ ((p3 ∨ p4) ∧ False)) ∧ (p4 ∧ p5)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264949160248985395208607535632 : (True ∧ ((False ∨ p2) → ((p4 ∧ (False → p3)) ∨ (((p4 → ((p5 ∧ True) → (((p2 ∨ True) → (p1 → (p4 ∨ p2))) → False))) → p3) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61154512417155812280882195569 : ((False ∧ ((p3 ∧ ((p3 ∨ p4) → p5)) ∨ (p1 ∧ (True ∧ (((((((p2 → p2) ∧ p4) ∧ True) ∧ p2) → True) ∨ (p1 → p5)) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52489757524115560651864077874 : (((p2 → (True ∨ ((p4 ∨ (((True → False) → (p1 ∧ p3)) ∧ False)) ∧ p3))) ∧ ((p1 ∨ p2) → ((p2 ∧ (p3 ∧ (p3 ∨ True))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104522949151219354092164361954 : ((((p4 → ((p5 ∨ (True ∨ (((p5 → ((True ∧ p5) ∨ (p3 ∧ p4))) ∧ p5) ∨ p3))) → (p3 ∧ p5))) ∨ True) ∨ (True ∧ p4)) ∧ (p2 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148608442766634769727651765174 : ((((True ∨ (((p2 ∧ p4) → p5) → (p2 ∨ p1))) ∧ p3) → (True ∧ (p1 → (False ∧ (p4 ∧ (True → p5)))))) ∨ (p4 → (False ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205275056653635382090011158978 : ((((p2 → False) → p5) ∨ (p2 ∨ p1)) ∨ ((((((((True ∨ p1) ∨ (p3 → (p3 ∨ (p3 → p5)))) ∧ p1) ∧ p2) ∧ p5) → p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312375173766413415301737450003 : (p2 ∨ (p3 → (((((p5 ∧ (True ∨ p1)) → p2) ∨ p4) → p2) ∨ (p2 → (p1 → (p1 ∨ ((((True → True) → p4) ∧ p1) ∧ (p4 ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



