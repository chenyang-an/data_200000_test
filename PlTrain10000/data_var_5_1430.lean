variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609581771724759862989069447023 : (((((p4 ∧ (p5 ∧ ((p4 → ((((p5 ∧ p2) ∧ (((p2 ∧ (False ∨ False)) ∨ (True ∨ p4)) ∨ p3)) → False) ∨ False)) ∧ p4))) ∨ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68593051544182157016146279323 : ((p4 → ((True → (((p2 ∨ p4) ∧ p5) → (False ∨ ((((True ∧ (p1 ∨ (True ∨ p1))) ∧ (p4 ∧ p3)) ∨ True) ∨ (p2 ∧ p4))))) ∧ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698619314968845329712294290971 : (((((p1 → (p5 ∨ p3)) ∧ ((p4 ∧ p4) ∧ (p1 ∧ (True ∨ p5)))) ∨ (((p3 → p2) ∨ (p4 ∧ p4)) ∨ (p5 ∨ (p2 → (False → p3))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38130033235367794135480259579 : (((((p2 → (False ∨ True)) ∧ ((p3 ∨ (p1 → ((True ∧ (p5 ∨ p2)) → (p4 ∨ (p1 → p5))))) ∧ True)) ∧ ((p4 ∧ p4) ∨ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614599246959025764284889076169 : (((((p1 ∧ ((True → (True → (p3 ∨ (False ∨ ((p2 ∨ (p4 ∧ p4)) ∨ p5))))) ∨ (p3 ∨ p1))) ∧ (p3 ∨ ((p2 → p4) → p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_49063378862389312220323578894 : (((((p2 ∧ ((p5 ∧ False) ∧ (p3 → ((((p3 ∧ p1) ∧ True) → False) ∨ p1)))) ∨ (False → True)) ∨ (p1 ∧ p4)) ∨ (False ∨ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205487341491844605701910171620 : (((False ∧ p5) ∧ (False ∨ (p5 ∧ p5))) ∨ (((p1 ∨ p4) ∧ False) → ((p5 ∧ (((p4 ∧ (p5 → p4)) → (p3 ∨ (False ∧ p3))) → p3)) ∨ p3))) := by
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
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336194667526333980782766819508 : (p1 → ((((((True ∨ True) → ((True ∧ p2) ∧ (p2 ∨ (((False → True) ∧ ((p5 ∨ p1) → p2)) → False)))) ∧ p3) ∧ p4) ∨ (False ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151876578663507367056030454988 : (((((False ∧ (((p5 ∨ p2) → (p2 ∧ p1)) ∨ (p5 → p2))) ∨ True) ∧ False) → (p3 ∨ ((False ∨ p3) ∨ p1))) → (p1 ∨ (p1 → (False ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14547227209915277232650829674 : (((((p5 → (((p3 ∧ (p3 ∧ p4)) → (((p1 ∨ False) ∨ True) → (True ∧ p5))) ∨ p1)) → ((p4 ∧ p5) → p1)) ∨ True) ∨ (p1 ∨ False)) ∧ True) := by
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
theorem thm_5_vars_219354609688320171955168095698 : ((p3 ∨ ((p1 ∨ False) ∧ p1)) → ((False ∨ (p4 → ((p5 ∨ p1) ∧ (((((p3 ∨ p2) ∧ False) ∨ p4) ∧ (True ∧ False)) → p5)))) ∨ (p2 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712415176993059214039859923667 : (((((p1 ∧ (False ∧ p2)) ∧ (p3 → True)) ∨ ((p2 ∧ p1) ∨ ((p4 ∧ (False → p2)) ∨ (p1 ∨ (p1 → ((True ∨ (False → p1)) ∨ p3)))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60019879114602624800179026612 : (((p1 ∨ p1) → ((p4 ∨ ((((((p5 ∨ False) ∧ p4) ∨ ((((p4 → p3) → p1) ∧ p1) ∧ (p3 ∧ False))) ∧ True) ∧ False) ∧ p4)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50173218143135137517164214076 : ((((((((p1 ∨ p3) ∧ p1) → (True ∧ p3)) ∨ ((((p1 ∧ p5) ∧ False) ∨ p2) ∨ True)) ∨ True) ∧ p4) ∨ (False ∨ (p2 → (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227474636602148883881213843759 : ((True ∧ (p3 ∧ p1)) ∨ ((((p5 ∨ (p4 ∨ (p5 ∧ False))) ∨ (((p1 → (p4 → (True ∧ p5))) ∨ p1) ∧ (p2 ∨ (p2 → False)))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613448798220104478901052217812 : (((((p2 ∨ (p5 → (((((((p3 ∨ (p3 ∨ True)) → p3) ∨ p2) ∧ (p2 ∧ True)) ∨ p5) ∧ p2) → (p3 → True)))) → (p5 → p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_136304068111978612556627742682 : (((((p2 → p2) ∨ p3) ∧ p3) ∧ (p2 ∨ ((p5 ∧ ((((True → p1) → (True → p5)) ∧ (False ∨ p3)) → p5)) ∨ p2))) ∨ ((p4 → p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157004026056521343132898409238 : (((((p3 → p3) ∧ p5) ∧ (((((p3 ∨ p5) → False) ∧ p2) → p4) → ((False → p2) ∧ p5))) ∨ p2) ∨ ((p1 ∨ p2) ∨ ((p2 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164447872401839611018175872228 : (((((False → ((False ∨ (p4 ∨ p5)) ∨ (p4 ∧ (p4 → False)))) ∧ (False ∧ p5)) ∧ p4) ∧ True) ∨ (False ∨ (True → (False ∨ ((True → p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165208880965504275553635044928 : ((((p4 → ((p5 ∨ ((p4 ∨ (p3 ∧ p1)) ∨ (p1 ∨ True))) ∧ p3)) → p4) ∨ (False → p5)) ∨ (p3 ∨ ((True ∧ p5) ∨ (False ∨ (p2 ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326179651874261639648513710398 : (p5 ∨ (p2 → ((((((p5 → False) ∧ p4) → (True ∨ True)) ∨ (p3 ∧ (False → p1))) → p5) ∨ ((((False → True) ∨ p5) ∨ (p3 ∨ p5)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24443909892055263437743783658 : ((((p2 ∨ p4) → True) ∧ (p3 → ((p3 → (True ∧ ((p5 → p3) → (p2 → False)))) → ((p1 ∨ ((p2 ∨ (p2 ∧ p1)) ∨ False)) ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144534542533356279477699860969 : ((((((p4 ∨ (p3 → p1)) ∧ ((p5 ∧ p2) → False)) ∨ (p5 ∨ (False ∨ p3))) ∨ (p3 ∧ p5)) ∨ (p1 ∨ True)) ∧ (True ∨ (False ∨ (True → p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354807284074524325852105642477 : (p5 → (((p5 ∧ (p4 ∧ (p4 ∨ p3))) ∨ ((p3 ∨ (True ∧ ((True ∧ ((p1 ∧ (p1 → ((p5 ∨ p5) ∧ p1))) ∧ p3)) ∧ p5))) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46078459943696232888252730761 : ((((((p5 ∧ ((p1 ∧ (p3 ∨ (p4 ∧ ((False → (p5 ∧ p5)) ∧ False)))) ∨ p2)) ∧ True) ∧ ((p2 ∧ False) ∧ p5)) ∨ p3) ∧ (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190880366008574974055815375631 : ((((True ∧ p4) ∨ ((p5 ∧ p2) → p1)) → (p5 ∧ False)) ∨ (True ∨ (((p1 → True) → ((p3 ∨ (p3 → True)) → ((p1 ∧ p3) ∨ p4))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671263416449739176477440904451 : ((((p4 ∨ (p1 → ((p3 → (False → p2)) ∧ (p3 ∨ (((p4 → ((p1 → p3) ∧ p5)) → p4) ∧ (p3 ∨ p3)))))) ∨ (False ∨ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171509918558275434619222870390 : (((((True ∧ ((((p2 ∨ False) ∧ True) ∧ p3) ∧ p2)) ∨ (p1 ∧ p1)) ∧ True) ∨ p3) ∨ (p2 ∨ (((True → False) ∧ (False → (p4 → True))) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150814082440077576077514463133 : (((((((p2 → False) ∨ (((True ∨ (p3 → p1)) → p4) ∧ p4)) → p3) ∨ (p5 ∨ p1)) → (p5 ∨ p4)) ∨ p5) → ((p5 ∧ p4) → (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49781270272135519388707350768 : (((p3 ∨ (((p1 ∨ p4) → (((((True → p2) ∧ False) ∧ (p4 ∧ p3)) → p4) ∨ (False ∧ p4))) ∧ (p4 ∨ p3))) → (p1 ∨ (p1 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350116146595078274641579141639 : (p4 → ((((p2 → (False ∧ p1)) → ((((False ∧ (False → p4)) → (p5 → (p4 → p2))) → p5) ∧ p2)) → (p1 ∨ (p2 ∧ (False ∨ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313912774917619086329448020805 : (p3 ∨ ((p2 → (((p1 ∨ p4) ∨ ((((True ∧ False) ∨ ((p2 → p3) ∧ p1)) ∨ (p5 → p5)) ∨ (p3 ∧ p3))) ∨ (p5 ∧ p1))) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193797052009146775416834091233 : ((p4 ∧ (False ∨ (p3 ∨ (True ∨ (p4 → (p3 ∧ p3)))))) → ((p4 → ((True ∧ (p1 → False)) ∧ (p3 ∧ ((p4 ∧ False) ∨ p3)))) ∨ (p3 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152994557961536757083818699382 : ((p1 ∧ (True ∨ ((((p1 ∨ False) ∨ ((p1 → (p5 ∧ (False → p5))) → (p3 → p2))) ∨ (False ∧ p5)) → p1))) → (((True → p2) ∨ p2) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46584285572480738337889994689 : (((False ∧ (((True ∧ ((False ∧ True) → ((p5 ∧ p1) ∨ (True → p5)))) → p5) ∧ (True ∧ (False ∧ ((p2 → True) ∧ True))))) ∧ (True ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600338428298437605598550999200 : ((((True ∧ (((((((p3 ∨ ((p2 → p5) ∨ p4)) → False) ∨ p2) → (p2 → (p1 ∧ p1))) ∨ p3) ∧ (p1 ∧ (p4 ∨ p4))) ∧ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735263418542381965381283090519 : ((((p3 ∨ p5) ∧ (p5 ∧ ((((((((p1 ∨ p3) ∨ (True ∧ True)) → (False ∧ p2)) ∧ p5) → (p3 → p3)) → (p3 ∧ p2)) → p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781143801036846633466651814180 : (((p2 ∨ ((p3 → p2) ∨ ((True → ((p4 ∨ (p3 ∨ p3)) ∧ p1)) → (((False ∧ ((p3 ∨ p5) ∧ p2)) ∨ p1) → ((p3 ∧ p2) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347097950629350258671475468538 : (p3 → ((((p1 ∧ (((((p5 ∨ True) ∨ False) ∧ p2) → p4) → True)) → False) ∨ p5) ∨ (((False ∨ p1) ∨ (p4 ∨ (p2 → (p4 → True)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263996171800482607962131601988 : (True ∧ ((p2 → ((((p5 ∨ p4) → (p1 → p2)) ∧ (True → p5)) → p4)) ∨ (((p4 ∧ p3) ∨ ((p2 → p4) ∧ ((p1 ∨ p5) ∧ True))) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299251607699965506097971475128 : (False ∨ ((((((p4 → p4) ∧ (p2 ∧ p1)) ∧ ((False ∧ (False → (p2 → p3))) ∨ (p3 ∧ p1))) ∨ True) ∧ (((p4 ∧ False) ∨ p4) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341718910086210125458074970657 : (p2 → (((p2 ∧ ((p3 → (False → (p4 ∨ True))) → p3)) ∨ (p4 ∧ ((p1 ∨ (p3 ∧ ((p3 ∧ False) ∧ p3))) ∨ (p5 ∧ p2)))) ∨ (True ∧ p2))) := by
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
theorem thm_5_vars_598253228018168861042412188506 : (((((True ∧ (p5 ∧ p1)) ∨ (((p1 ∧ True) ∧ ((True ∨ p1) ∨ (p2 ∨ ((p1 → p1) ∨ p4)))) ∨ (((p1 ∧ p5) ∧ p4) ∨ False))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617213896424066987422325032364 : ((((((p2 ∧ p5) ∧ (p2 ∧ ((True ∧ p5) ∧ False))) ∨ (((((True → (True ∨ False)) ∧ p3) → (p4 ∨ p5)) → (p5 ∨ p5)) ∧ False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336204204568937185390351641772 : (p1 → (((p3 ∨ ((((p4 → (True ∨ (p2 ∧ (p1 ∧ False)))) → True) ∧ p3) ∧ (p2 ∧ (p2 ∨ ((p4 ∧ True) ∧ False))))) ∨ (True ∧ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705636887683590472164701896680 : (((((p4 → (p3 ∨ ((False ∧ p4) ∨ True))) → False) ∧ (False ∧ ((False ∧ p2) ∧ ((False → (((p1 ∨ (p4 ∧ p3)) ∨ p4) → False)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352091530669910748116560833379 : (p4 → ((((p2 ∧ p5) ∧ (p5 → p3)) ∧ False) ∨ ((((((False → p2) ∧ p2) ∨ True) → True) ∨ p4) → (p2 ∨ ((p3 ∨ p2) ∨ (False → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115097575171040932757639355548 : ((((((p4 ∨ p5) ∨ ((False → (p2 → False)) ∧ p4)) ∨ p5) ∧ p4) → (p1 → ((p3 ∨ p4) → ((False ∨ p2) ∨ (True ∧ True))))) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646047459407949811935861916169 : ((((True → (True ∧ (((p4 → p3) ∧ (p1 ∨ (p4 ∨ p2))) → ((p3 ∧ (p1 ∨ p2)) ∧ (p1 ∨ (p3 ∧ (True ∨ (p3 ∨ p4)))))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171552731261569913282676685342 : (((((p3 ∨ ((p2 ∨ ((p4 → p2) → p4)) ∨ p1)) → (p1 → p3)) → False) ∨ True) ∨ (p4 ∨ (False → (((p1 ∧ (p4 → False)) ∧ p4) ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309954924498976475803003360980 : (p2 ∨ (((p2 ∧ ((False ∧ p5) → (((p2 → ((p4 ∨ False) ∧ p1)) ∨ p3) ∨ (p4 ∧ p3)))) → p1) → ((((False ∧ p1) ∨ p3) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264319458757013820377647138032 : (True ∧ ((p1 ∨ (p4 ∨ (p5 ∨ (p2 ∧ p4)))) → (((((p2 → False) ∨ p1) ∧ p1) → (p5 ∨ (p4 ∧ (p4 ∨ (True → p2))))) ∨ (p1 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h25 := h23 h24
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h19
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9628438594288243633127788501 : ((((p5 ∨ p4) ∧ ((((p2 → ((p2 ∨ ((((p3 → (False ∨ (p5 ∧ True))) ∧ p1) ∨ p3) ∧ True)) ∨ p2)) → p3) ∧ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114194650839047830836471163381 : ((((True ∧ (p1 → (p4 ∧ (p5 ∨ (p5 ∨ (p5 ∨ p4)))))) → (((True → (p4 → p3)) ∧ p5) → p4)) → ((True → p2) ∧ p3)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168042427448770908387881367580 : ((((p2 → p1) ∧ ((p3 ∧ p5) ∨ p2)) → ((p5 ∨ ((False ∧ p4) ∨ p5)) ∧ (p3 → p4))) → (((p1 ∨ False) ∨ (p1 → p1)) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215595631061904737020994978739 : ((p5 ∧ (p1 ∨ (p4 ∨ p4))) ∨ (p3 → ((True ∧ ((((False ∧ p1) ∧ (p2 ∨ (((p2 → p1) ∨ p4) ∨ p4))) ∧ p3) ∨ True)) ∧ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111764987097259961058194789489 : ((((((((p4 ∨ p2) ∧ True) → True) ∨ (True ∨ False)) → (p2 ∧ (((p4 ∧ (p4 ∨ p1)) → p5) ∧ True))) ∧ (p2 ∨ False)) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228460538761184571476145353303 : ((False ∨ (p3 ∨ p3)) ∨ ((((p5 ∨ (p2 ∧ p1)) ∨ (p3 → (p2 → (p3 ∨ ((False ∧ p2) → p5))))) → p1) ∨ ((p5 ∧ False) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_322266844195969496160592077732 : (p5 ∨ (((p4 ∧ (((((p3 ∧ ((p5 → p3) → p2)) ∨ p4) ∧ (True ∨ ((False ∧ p4) → p3))) ∨ (p3 ∨ p3)) ∨ (False → p4))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218939363041070047912733576558 : ((p3 ∧ (p4 ∨ (p5 ∧ p5))) → (((((p3 ∨ (p3 → (True ∧ (p1 ∧ True)))) ∨ p1) → ((p1 ∧ ((p1 ∧ p2) ∧ p5)) ∧ p3)) ∨ True) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231973342791520279796915792095 : (((p1 ∨ p5) → p1) → (((p5 → p5) → (p3 → (((((p4 ∨ True) ∧ (p5 ∧ (p1 → p4))) ∧ p1) ∨ True) ∧ True))) ∧ (False → (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55203753588712596457220828455 : (((((p3 ∨ p2) ∨ p2) ∧ (False ∨ p1)) ∨ ((p1 → (p1 ∧ ((p4 ∧ p5) ∨ ((False ∨ (False ∨ ((True ∨ p1) ∨ p4))) ∨ p2)))) ∨ p3)) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731209261559410180851806517659 : ((((p3 ∨ (p3 ∧ p1)) → (((p3 ∨ p5) → (p3 ∧ (((((p1 → (p2 → False)) ∧ p5) ∧ p1) ∨ (p4 → p3)) ∧ True))) ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233938696595015639071122311695 : ((p4 ∨ (p4 → p4)) → (p3 → (((((p2 → (((p5 → p5) ∧ (True → False)) ∧ p4)) ∧ (p2 ∧ True)) → (p1 ∧ p5)) ∧ (False ∧ False)) ∨ p3))) := by
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
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135634495015100846757587938623 : ((((((True → p4) ∧ ((((False → False) → True) ∨ p4) → (True ∨ True))) ∧ p1) → p1) → (((p2 ∧ p4) → True) → False)) ∨ (True → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349026483056214895612286841893 : (p3 → (p5 ∨ ((((((p4 ∨ (p1 ∨ (p2 → p4))) ∧ True) ∧ False) ∨ p5) ∨ (((p5 ∨ True) ∨ False) ∧ (False → ((p5 → p5) → p1)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245750281872425099209423078990 : ((p3 ∧ p2) ∨ (False ∨ ((((((p4 ∨ p4) ∨ False) ∨ ((((p5 ∨ p3) ∧ p1) → (p4 ∨ p3)) → p5)) ∨ False) ∧ (p5 ∨ p1)) → (p1 ∨ p5)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707306701602163289971018045763 : ((((((True ∧ (p2 ∧ p4)) ∨ False) ∨ (p1 ∧ False)) ∨ (False → (((p4 → False) ∧ ((p2 → p5) → ((p5 → False) → p3))) ∧ (True → p1)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704775901509949361103886452578 : ((((p4 ∧ (p5 → ((((p3 ∧ p3) ∨ p5) ∨ p5) → False))) → (p4 ∧ ((p3 ∨ (p4 ∧ True)) ∧ ((p3 ∨ (p3 ∨ p1)) ∨ (p5 → p2))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (((p3 ∧ p3) ∨ p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49181520190053495801312000363 : ((((True ∧ ((p2 ∨ False) ∧ False)) ∨ (((True ∨ p2) ∧ p4) → ((((p3 ∧ (False ∧ p1)) ∨ False) ∨ p4) ∧ True))) ∨ (p3 → (p4 ∧ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752265497027903652169532424009 : (((True ∧ (p5 → ((((p5 ∨ False) ∨ ((p1 ∨ p4) → p2)) → (False ∧ (((p5 ∨ True) → ((p1 ∧ p1) ∧ False)) ∧ (p4 → p5)))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139622419432862364653798133391 : ((((p1 → (False ∨ ((((p4 ∧ p1) ∨ p2) → p1) → True))) ∨ (((p5 → (p2 → (p3 ∧ p2))) → False) ∨ p3)) → p1) → (False ∨ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → (False ∨ ((((p4 ∧ p1) ∨ p2) → p1) → True))) ∨ (((p5 → (p2 → (p3 ∧ p2))) → False) ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135437160518806538594851571444 : (((p2 → ((p1 ∧ p4) ∨ (p3 ∧ ((p3 ∨ (p4 ∨ True)) ∨ (((True → False) ∨ p1) → p2))))) ∨ (p5 → (p5 → True))) ∨ (p3 ∨ (p4 ∨ p3))) := by
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
theorem thm_5_vars_199769388474771075972749479338 : (((p2 → ((p2 → p5) → (p5 → True))) → False) → ((((p3 ∧ p4) → (True ∨ ((p2 → (p4 → False)) ∨ False))) → (p3 ∨ (p5 ∨ p1))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p2 → p5) → (p5 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315459762403718709436267864291 : (p3 ∨ (((p5 ∨ p5) ∧ True) → ((p5 → (((((p5 ∧ ((p3 → p1) ∨ False)) → p4) → p3) → False) → (p3 ∨ ((p3 ∧ p2) ∧ p1)))) ∨ True))) := by
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
theorem thm_5_vars_119550764601458432633041363071 : ((p5 → ((p3 ∨ (True ∧ ((((True ∧ (p3 ∧ p3)) ∨ ((True ∧ (False → True)) ∧ p3)) ∨ p4) ∧ p1))) ∨ ((True ∨ p5) → True))) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119806090634684880167544489313 : (((((((p3 → (p5 → p5)) → False) ∨ ((True ∨ ((p5 ∨ True) ∧ False)) ∨ (False ∧ p1))) ∧ (p2 ∨ (False ∧ True))) → p3) ∧ p1) → (p2 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p3 → (p5 → p5)) → False) ∨ ((True ∨ ((p5 ∨ True) ∧ False)) ∨ (False ∧ p1))) ∧ (p2 ∨ (False ∧ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356020108031496480759710860980 : (p5 → (((p4 ∨ (p3 ∨ (p3 ∨ ((p2 → (((p3 → True) ∨ p1) ∧ p2)) → (p3 ∧ (False ∨ p1)))))) → p4) ∨ ((p4 → p5) ∨ (False ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156971795770201369536988775392 : (((((((p5 ∨ ((p3 ∨ False) ∨ p4)) → True) → p4) ∨ p5) → ((p5 ∧ (p4 → p2)) ∨ p4)) ∨ p1) ∨ (p4 ∨ (False → ((p3 ∧ p5) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193584349788072775340363838673 : (((True → p1) → ((((p3 → p5) ∧ True) ∧ p4) ∧ p1)) → (p1 → ((p1 ∧ (p4 ∧ (((False → p2) ∨ p1) → (p1 → p1)))) ∧ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (True → p1) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216842628447353496376213574700 : (((p5 ∧ (p2 ∨ p5)) ∧ True) → (((((((p4 → False) → (p3 ∨ p2)) ∧ p1) ∨ p3) ∨ (p5 ∧ True)) ∨ ((p3 → True) ∧ p2)) ∨ (p5 ∧ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40727759317584196657156425089 : (((((p3 → (p1 → ((p5 → True) ∧ p5))) → (((((p1 → (p4 ∨ p4)) ∧ False) ∨ p2) ∨ (False → (p2 ∧ p5))) ∧ p2)) → False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685517912429636103752702212 : ((((p2 ∧ (p5 ∨ (p1 ∧ p1))) ∨ (p1 ∨ ((True ∨ (False ∧ p4)) ∧ p2))) ∨ (False → (((p2 → p1) ∧ (p5 ∧ p5)) ∨ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164928114664348353770567664493 : ((((((False → (p1 → (p5 ∨ p2))) ∨ p4) → (p4 ∧ ((p2 ∧ p2) ∨ False))) ∨ False) → False) ∨ ((p4 ∨ p2) ∨ ((p5 ∧ (p3 ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328298949061840315286532719803 : (True → (((True ∨ p3) ∧ ((p3 ∨ (True ∧ (((((p4 → p4) ∨ p4) → (p5 → p4)) ∨ False) ∨ p3))) → p2)) ∨ (p1 ∨ ((False ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_355586257277706258431317688971 : (p5 → (((p2 ∨ ((p1 ∨ ((p4 → False) → (True ∧ True))) ∧ p2)) → ((((p5 ∨ True) → ((p1 ∨ False) → p3)) ∧ p4) ∨ p2)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_42529194494825536492451569572 : (((p1 ∨ (((((False ∨ (p1 ∧ p5)) ∨ (p2 → ((True ∨ ((p1 ∧ (False ∧ (p3 → True))) ∧ p1)) → p5))) → p4) ∨ False) ∨ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731642293417044273183127152973 : ((((p1 → (p2 → False)) → ((((True → p1) ∧ ((p5 → p4) → p3)) ∧ ((p1 → p2) ∨ (p5 ∨ p3))) ∨ (p4 → ((p3 ∨ True) ∨ False)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133620087198187638443102021899 : (((((p5 → ((p3 ∧ p4) ∨ (False → p3))) ∧ (True ∨ (p1 ∧ ((p2 ∨ p5) → ((p2 ∧ False) ∧ p5))))) → p3) ∧ False) ∨ ((p2 → p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327196604713419758278794000574 : (True → ((p4 ∨ ((((p5 → (True ∨ (p2 ∨ p1))) → (p1 ∨ (True ∨ p1))) ∨ True) → (p4 ∧ (((False ∨ (p5 ∨ p4)) → p3) → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46273805560321155342947769803 : (((((((True ∨ True) → (((p4 ∨ p5) ∧ p5) ∨ False)) → ((True → p3) ∨ p1)) ∧ (p3 → p5)) ∧ ((p5 ∧ p1) ∧ p2)) ∧ (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143250903263304061700025762824 : ((p3 → ((True ∨ ((p2 ∨ p5) ∧ (p5 ∨ (True ∧ ((p5 ∨ p5) ∧ (p2 ∧ (True ∧ (False → p1)))))))) ∧ (p5 ∨ False))) → (p1 ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52671952796546411568869112519 : (((False ∨ (((p2 ∧ p1) → (p4 → p3)) → (p3 → ((p4 ∧ p2) ∨ p1)))) ∨ ((p3 ∧ False) ∧ ((p4 ∧ p2) ∨ (p4 → (True → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190730174915735272287082040638 : ((((False ∨ False) ∨ (p5 ∧ (p2 → p5))) ∧ (p3 ∨ p3)) ∨ (((p5 ∨ True) ∧ p3) ∨ (((p2 ∧ p4) ∨ (p1 ∨ (p4 → (p2 ∨ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239600115449911654206304987577 : ((p3 ∨ True) ∧ (((False ∨ (True ∨ (p5 → True))) ∧ p5) → (((False ∧ p5) → p1) ∧ ((False → p2) → ((((p3 ∨ False) ∨ False) ∨ p5) ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186220685133723009571763788316 : (((p1 → (((p1 ∧ True) → (p5 → (p4 ∨ p1))) → True)) ∨ p2) → (((p3 ∧ p5) → False) ∨ (((((p1 ∧ p3) → p2) ∧ False) ∨ p5) ∨ True))) := by
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
theorem thm_5_vars_185366795443615823504784927619 : ((p5 ∧ (((((p1 → p5) → p4) → p5) ∨ (False → p5)) ∧ p1)) ∨ (p3 ∨ ((p1 ∧ (True ∨ ((p2 ∨ (p3 ∧ True)) → p4))) → (p5 ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159968345456995238159424914283 : ((((p5 ∨ ((p3 → (((p2 → p2) → p4) → (p4 ∨ True))) → p5)) ∨ (p3 ∧ (p3 → p5))) → True) → (p3 → (((p4 → p3) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167385242534919819404289415945 : ((((p5 ∨ (p4 → p4)) ∨ ((p2 ∨ False) ∨ ((p5 ∧ True) ∨ ((p3 ∧ p1) → True)))) → p3) → (p3 ∨ (((False ∧ False) ∨ True) ∧ (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (p4 → p4)) ∨ ((p2 ∨ False) ∨ ((p5 ∧ True) ∨ ((p3 ∧ p1) → True)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739106811635486806410264485805 : ((((p3 ∧ p5) ∨ ((p5 ∧ (((((True ∨ p1) ∨ p2) ∨ False) ∧ (False → False)) ∨ (True → True))) ∧ ((False → (p3 ∧ p5)) → (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



