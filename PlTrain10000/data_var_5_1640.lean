variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53276268348305547696058218577 : (((p2 ∧ (((False ∨ (True ∨ False)) → False) ∧ ((p3 ∨ p2) → p2))) ∨ ((p3 ∨ True) ∧ ((p5 → (p1 ∧ (p1 ∧ p3))) ∨ (p5 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666612289742601564319542928539 : (((((((((False ∧ (p1 ∨ p5)) ∨ True) → (p1 ∨ p3)) ∧ p1) → p4) ∨ (True ∧ (p1 ∨ ((p1 ∨ True) ∨ p1)))) ∧ (p3 ∨ (True ∧ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304678593479782193333673406341 : (p1 ∨ ((((((p3 → p4) → p2) ∧ p4) ∧ (False ∨ (((False → (((p4 ∨ p1) ∧ p3) ∧ p1)) ∧ p1) ∨ (p5 ∨ p4)))) ∧ p3) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232396778243703234007052656002 : (((p5 → p3) → p3) → ((p3 → (p5 ∧ ((p4 ∨ (((p1 → True) ∧ True) ∨ p1)) ∨ False))) → ((((p5 → (True → p4)) ∨ False) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316958883918139745301186218578 : (p3 ∨ (p2 → (p4 ∨ ((((True → p5) ∧ ((((p5 ∨ True) → p4) ∨ (True → p2)) ∨ (False ∧ p4))) ∨ (p4 ∨ ((True ∨ True) ∧ p2))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314332011279741705132935166387 : (p3 ∨ (((p5 ∨ p2) ∨ (p3 ∧ ((True → ((p4 ∨ True) ∧ ((((p2 ∧ p3) ∨ True) ∧ (False ∧ p4)) ∨ False))) ∨ p2))) → ((p4 ∧ True) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
theorem thm_5_vars_476381737878567304783993509544 : ((((((p5 → p2) ∧ p1) ∧ ((p4 → p4) ∧ (p1 ∧ p3))) ∨ (p5 → (p5 → ((p1 ∨ ((p1 → p5) ∧ (p5 ∧ False))) ∨ (False → p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38400661517158071951890299537 : ((((p3 ∨ ((p5 ∨ p4) ∨ ((p2 ∧ p3) ∨ (p2 ∧ ((p4 ∧ p3) → (False ∧ p4)))))) → ((p1 → ((p5 ∧ p4) ∨ False)) ∨ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704425357976229314528557268836 : ((((((p1 ∧ False) → p2) ∨ ((p1 ∨ True) ∨ (p3 → p2))) → ((((True ∧ (False ∨ p5)) ∨ p3) ∧ ((p1 → p3) → (p2 ∨ p4))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197198333710269152405707874815 : ((((p4 → ((p1 → p3) ∨ p4)) ∧ True) → p4) ∨ ((p1 → (((True ∧ True) → p1) ∧ (((True ∨ p5) ∨ (False ∧ p4)) ∨ p1))) ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234602827546825862301099144368 : ((p3 → (p3 ∨ p5)) → ((True → p4) → (((p5 → (p2 ∧ ((p4 ∧ p3) ∨ ((p3 ∧ (True ∧ False)) → True)))) → p4) ∨ ((p2 → p1) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632469109949693869394497929498 : (((((p2 ∨ (p4 ∧ ((((True ∧ ((p1 ∨ True) ∨ p4)) ∨ p5) → ((p1 ∧ p4) ∧ (p5 → (p5 ∨ p5)))) → (p4 ∧ p1)))) → False) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118163799047433858246614421419 : ((False ∨ ((True ∧ p4) ∧ (p4 ∧ (p4 ∨ (p5 ∨ ((((p2 → p2) ∨ ((p1 ∧ False) ∧ p3)) → (p5 ∨ (False → p5))) ∧ p1)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54730893495632466293427491216 : (((((p3 ∧ False) → False) ∨ ((p3 → p4) ∨ False)) → ((p5 ∨ ((True → (((False ∨ p5) ∨ p4) ∧ False)) ∨ True)) ∨ ((p3 → p4) ∨ p1))) ∨ p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49366415323201142275956438299 : (((p4 → (((p5 ∧ (p2 ∧ ((False ∨ (((p2 ∨ True) ∨ ((p2 ∧ p4) → p3)) → p1)) ∨ p2))) ∨ True) ∧ True)) ∨ (p2 ∧ (p5 ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148894606887940716398450319933 : (((False ∧ (p3 → (p2 → p2))) ∨ (((p2 ∧ (((p1 → (False ∧ p5)) → p4) ∨ False)) ∨ (p4 → p4)) ∧ False)) ∨ (True ∨ (p2 ∧ (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148113540439997696736197921864 : (((((p5 → (p4 ∧ (p3 ∧ (False → p3)))) ∧ p5) ∨ ((True ∧ p3) ∨ ((p3 → False) ∧ False))) → (p5 ∧ False)) ∨ (((p4 → False) ∧ p4) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45871217617689554730460101722 : (((p3 → ((((p3 → ((p3 ∨ (p3 → True)) ∧ p2)) → True) → ((p3 → (p2 ∧ p5)) → p4)) ∧ ((p1 ∧ p1) ∨ (p3 → p4)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300558072599928458579403047307 : (False ∨ ((((p2 ∧ p1) ∨ p5) ∧ (((p4 ∨ p4) ∨ (p5 → p4)) → ((p3 ∨ (True ∨ p4)) → (p2 ∨ p1)))) ∨ ((p3 → (p5 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172894687228729745925877853362 : ((p2 ∧ ((((p2 → p5) ∨ ((p4 ∨ ((p3 → False) → True)) → p3)) ∧ p4) ∧ p5)) ∨ (((True ∧ (False ∧ (p5 → (p4 ∧ True)))) → p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65297901043167464418386426507 : ((p3 ∨ (((((True → (p1 ∨ (False ∨ p3))) → p4) → ((p1 → (((p3 ∨ p5) ∧ True) ∧ p1)) ∧ (p3 ∧ True))) ∨ p1) → (p1 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698085760594925784631531663164 : (((((p1 ∧ (((False → p5) ∨ p3) → (p5 ∧ (p4 → False)))) ∨ p4) ∨ (((p3 ∧ False) ∧ (((p5 → False) → p2) ∨ (p1 ∧ p2))) → False)) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586182224954528555267943131761 : (((((((((p4 ∧ (p1 → p5)) ∧ True) ∨ ((p3 → p4) ∨ p5)) ∨ p2) ∧ (((p1 ∧ p5) ∨ False) → (p3 ∧ (p4 ∨ p2)))) ∧ p4) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149074966563339498463334669604 : ((((p5 → p4) ∨ p3) → (p2 ∧ (((False → ((p5 ∨ True) → (p3 → ((True ∧ p2) ∧ p5)))) ∧ False) ∧ False))) ∨ (p3 → (False → (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730718450169592603708063279310 : ((((p3 ∧ (p2 → p4)) → (((p1 ∨ (False → (True ∧ (p1 ∨ ((False ∧ True) ∨ (True ∨ p3)))))) → (p5 ∧ ((p4 → p2) ∨ p5))) ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264464587001795612142420240536 : (True ∧ ((p3 → (p3 ∧ (True → p2))) → (((p3 → True) → (False ∧ (False ∧ (p5 ∧ ((p4 ∧ p2) ∨ (p2 ∨ (p2 ∨ (True ∨ p3)))))))) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148395435645425912665855188816 : (((p4 ∧ ((False ∧ False) ∨ (p3 → (((False → (p1 → False)) ∨ p5) ∧ p1)))) ∨ ((p3 → (p5 → p4)) ∧ True)) ∨ (p5 ∨ (p4 → (p4 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142933816989632957293942625591 : ((p5 ∨ ((((p5 → p2) → (p5 → (p5 → p3))) ∧ True) ∨ (p1 → (((p5 ∨ (p2 ∨ (True ∨ p5))) → p2) ∧ p1)))) → (p2 ∨ (p1 → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113935722698836538816148971458 : ((((p4 ∧ ((True ∨ ((p1 → True) → p3)) → False)) ∨ (p2 ∧ (p4 ∨ (True ∨ (True ∨ (p1 → p5)))))) ∧ ((p1 ∧ p4) ∧ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61258004006563101451554031219 : ((False ∧ (False ∨ (((p4 → p1) → ((((((((p1 ∧ True) ∧ (p4 ∨ p1)) ∧ p5) ∧ p3) → p3) ∧ p1) ∧ (p5 → False)) ∨ False)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318651958886878945243174024717 : (p4 ∨ ((p1 → ((p2 → ((((p5 → (p1 ∧ p1)) ∨ p1) ∨ p5) → ((p3 → p4) ∧ ((p4 ∨ p2) ∨ (False → p4))))) ∧ p2)) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47277045304518687846023872455 : ((((((p4 ∨ p5) → p4) → p3) ∨ (((p3 ∨ p4) → p4) ∧ (p4 ∧ (p1 ∨ ((False → True) ∨ (False ∧ (p2 → p1))))))) ∨ (False → p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42223566943672992403057401120 : (((False ∧ (((p4 ∧ ((((p1 ∧ (((True ∧ p2) ∧ p1) ∨ (False → (True → p1)))) ∨ p4) ∧ p3) ∨ p4)) → p5) → (p4 ∧ p5))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60173147602738306350271791286 : (((p5 ∨ False) → ((((p3 ∨ (p4 ∨ p3)) → False) → (True → ((False → (p2 ∧ p4)) → (False ∧ p5)))) → (p1 → (p5 → (p5 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598675421425822251230957691013 : (((((p1 → (False ∨ False)) → (p2 → (((False ∧ (p5 ∧ p3)) ∧ ((p2 ∧ (p1 ∧ (p1 → False))) ∨ (True ∨ p4))) ∨ (p4 ∨ p5)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50262823030725705034442639250 : (((((p3 ∧ (((((p2 ∨ (True → p3)) ∧ p5) ∧ p5) ∧ (p1 → False)) ∧ p5)) ∧ True) ∧ (p2 ∧ p5)) ∨ ((False ∨ p5) → (False ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116983489501604814713010663951 : (((p5 ∧ p2) → ((p1 ∨ (p4 ∨ (False ∨ (((p3 ∨ False) ∧ p5) ∨ p1)))) ∨ (True ∧ (True ∨ ((True ∧ (p5 → p2)) ∧ False))))) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40451747396127352410848806966 : (((((True ∨ ((p3 → p3) ∨ (p1 → p4))) → (((p3 → p3) → False) ∧ (((False ∧ p1) → (False → (p3 → True))) ∧ p4))) ∨ p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16951567387340806936179633582 : (((p2 ∨ ((True ∧ (((p4 ∨ (False ∨ ((p5 ∨ p3) → True))) → p3) ∨ True)) ∧ (((p3 ∨ p1) ∧ p4) ∧ p1))) ∨ (p5 → (p2 → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79325879537242440366912658120 : ((((((True → (((False ∨ p5) ∧ ((p2 ∨ (p3 ∨ p1)) ∨ p1)) ∧ p4)) ∨ (p4 → (p2 → (p3 → p2)))) ∨ False) → False) ∨ (p4 ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((True → (((False ∨ p5) ∧ ((p2 ∨ (p3 ∨ p1)) ∨ p1)) ∧ p4)) ∨ (p4 → (p2 → (p3 → p2)))) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h3
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55713791637666043957501168533 : ((((p2 → (True ∨ p1)) ∨ True) ∧ (p1 ∨ (((p4 ∨ (((p5 ∧ p5) ∨ p5) ∧ ((p1 → True) → False))) → (p4 ∨ p3)) ∨ (True ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325817536888352502379792721098 : (p5 ∨ (p3 ∨ (((p1 ∨ ((False ∨ (p3 → p1)) → p2)) → (False → p5)) ∧ ((False ∨ (True ∧ (((p1 → p1) ∨ p5) → (p1 ∨ True)))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41033238273667292043610082398 : ((((((p1 → ((p2 → (p4 ∨ p3)) → (p5 ∧ (((True → p4) ∨ p5) → p3)))) ∨ p5) → ((p5 → p5) → p3)) → (p4 → p1)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395632050518398541249739797082 : ((((p2 ∧ ((p1 ∨ (p5 ∨ p1)) → (False ∧ ((p3 → p2) ∨ ((p3 → True) → (p4 → ((((p3 ∧ p1) → p2) → p1) ∧ True))))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_52206496885145203370576076821 : ((((p4 ∨ p3) ∧ ((p4 ∧ p5) ∧ ((((p4 ∧ (False ∧ p1)) → False) ∨ p1) ∧ p1))) → (((p5 → p5) → (p4 → p3)) ∨ (p5 ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h15.left
    let h19 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h17
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48383414803714543420665456911 : (((True → ((p4 → True) ∨ (True ∧ (p2 → ((p3 → (((True ∨ p4) ∨ (True → (p4 ∧ p4))) → (True ∧ p5))) ∨ True))))) → (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41657978076288710064617856524 : ((((p4 ∧ ((p1 ∨ p5) ∨ (p4 ∧ p5))) ∧ (((False → p1) ∨ (p2 → True)) ∨ (p5 ∨ (False → (p5 ∧ (p4 ∨ (p2 ∧ True))))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499710262676976376395787721934 : (((((False ∨ p1) ∨ p3) ∨ (((((True ∧ False) → (p4 → (False ∧ (p2 ∨ (p2 → (((p2 ∨ True) ∨ p4) ∧ True)))))) → p4) ∧ p5) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50397819241089696824091292474 : ((((p2 ∨ p2) → ((p2 ∨ True) → (p4 ∨ (((p4 ∨ p5) → p4) ∨ (p1 → (True ∧ (p1 → p3))))))) ∨ ((True ∨ (p3 → p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214910013363573434489815880177 : (((p5 → False) ∨ (p2 ∧ False)) ∨ (((p1 → True) ∧ (p5 ∧ p2)) ∨ (((p4 ∨ (True ∨ p1)) → (True ∧ (p3 ∧ p3))) ∨ ((p5 ∧ p4) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171828408996117531671046977177 : (((((p1 ∧ p4) ∨ True) ∧ ((False ∨ (False ∧ (True → p4))) → (False → p3))) → p1) ∨ (((False → (False → p5)) ∨ True) ∨ ((p4 ∨ p3) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689120560191975509969528989636 : (((((((((False ∧ (False → p3)) ∧ p1) → (p2 → (p4 → p3))) ∧ True) ∧ p4) → p5) ∨ ((p4 ∨ True) ∨ ((False ∧ p5) ∨ (True ∧ True)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_166478226814897174054244548547 : ((p3 ∨ ((((False → ((p2 ∨ p2) ∧ (False → (p5 → p2)))) ∧ p5) → (p1 ∧ p2)) → p3)) ∨ ((p1 ∨ p5) → (p1 ∨ (p3 → (p3 ∨ p1))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57720058402923478603056197534 : ((((True ∨ p4) → False) → ((p5 ∨ (p4 ∧ True)) ∨ ((p5 ∨ (((p2 → (p2 ∨ p1)) ∨ (((p5 ∨ p4) ∨ p3) ∧ p2)) ∨ p1)) → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116837417058233427475910152848 : (((True → False) ∨ ((p3 → p2) → (((p3 → p4) ∧ (p1 ∧ ((False → p3) ∧ p1))) ∨ ((p4 ∧ (True ∨ (p4 ∧ True))) ∨ False)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114470801369895363372382537085 : (((((p5 → (True ∧ ((((p1 ∧ (True ∨ False)) ∧ p2) ∧ True) ∨ p4))) → (p4 → p1)) → p2) → (True → (p1 ∨ (False ∧ False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199674281432222858947490508756 : ((((p5 ∨ p3) ∨ ((False ∧ p5) → False)) → False) → (((p5 ∨ ((((p2 ∧ (p2 ∨ p5)) → p5) → ((True → p4) → False)) ∧ False)) ∧ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p3) ∨ ((False ∧ p5) → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351757279332646564160846402548 : (p4 → ((((p1 → (p1 → (((p2 ∨ p1) → p2) ∨ p4))) ∨ p2) ∨ (p4 → p5)) → (True → (p1 ∨ ((True → (False → False)) → (p2 ∨ p4)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147792380277934847823133413152 : (((True ∧ (p2 ∨ (True ∨ (p4 → ((False → ((p1 → (False ∨ p2)) → ((p3 ∧ p4) ∨ True))) ∨ p3))))) → p4) ∨ (p2 → (False → (p3 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142577020577879234463924120096 : ((False ∨ (((((((False ∨ (p4 ∧ ((p2 ∧ (True ∧ p1)) → p5))) ∨ (False ∨ False)) ∧ p1) ∨ p5) → p3) → p2) ∨ p3)) → ((p5 ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_684020133228404141098113725226 : ((((((p4 ∨ True) ∧ ((True → ((p2 ∨ p5) → p2)) ∧ (p1 → (p1 ∨ (p2 ∨ p5))))) → False) ∨ ((False ∧ p5) → (p1 ∧ (p5 ∨ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651076305385684558114301962843 : (((((p3 ∧ (False ∧ (p1 ∧ p3))) ∧ ((((False ∨ p3) ∧ (p3 ∧ p5)) ∨ p5) ∨ (((p4 → p5) ∨ (p1 ∨ False)) → True))) ∧ (p3 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56677112824683371244645798454 : ((((p2 → p5) ∧ True) ∧ (((True ∨ (p5 ∨ (p2 ∧ (True ∧ ((p2 → p4) ∧ ((False ∧ False) → (False → (p4 ∨ True)))))))) → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698739384282455611324182863357 : (((((p2 ∧ p2) ∨ ((((p2 ∧ p1) ∨ p1) → (p2 ∧ p3)) ∨ p1)) ∨ (((p3 → False) ∨ False) → (p2 → (p1 ∧ ((p4 → True) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59172496924633152148361920801 : (((False ∨ p4) ∨ ((p5 ∨ (((p1 → (p5 → (p1 ∨ p4))) ∨ (False → True)) ∧ p2)) ∨ ((p2 ∧ (p1 ∧ ((False ∨ p4) ∧ p1))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45126390398194721424118683429 : ((((False → p2) → ((p4 → (False → ((True ∨ (p2 → p3)) → p5))) ∨ (((True ∨ p2) ∧ (p2 ∨ p4)) → (p1 ∨ (True → p4))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160652425897576597068704737915 : ((((((p4 ∧ (p1 → False)) ∧ p1) ∧ p4) ∨ (p2 ∨ p1)) → ((p4 ∧ False) → (p5 → (p5 ∧ False)))) → (p3 ∨ (True → ((p3 → p2) ∨ True)))) := by
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
theorem thm_5_vars_191860387339683613490146997091 : ((p4 ∨ (((((p2 ∧ False) ∨ False) → p2) → False) ∨ p5)) ∨ (((p1 ∨ p5) ∨ (p1 → True)) ∧ (p5 ∨ (True ∨ ((p3 ∧ p3) → (p5 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173202865700176754948004221561 : ((p5 ∨ ((p4 ∧ (False → ((p5 → (p4 → (True ∧ (True → p2)))) ∨ p5))) → False)) ∨ (((True ∧ False) → (p3 ∧ p5)) ∨ ((True ∨ p5) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244697073333808863354131879855 : ((p1 ∧ True) ∨ ((((False ∧ p5) → p2) → ((p2 → (p3 → False)) ∨ (False → p5))) ∨ ((p1 ∧ p4) → (False ∧ (p3 ∨ ((p3 → False) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615352469828165841771717783009 : ((((((p2 ∨ (p4 → ((True ∨ (False ∨ True)) ∨ False))) → (((p4 ∧ p1) ∨ True) → p3)) ∨ ((p2 ∧ True) ∨ (False ∧ (False ∧ p1)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157777592079583472467415496828 : (((((((((p3 ∧ p2) ∧ p4) → p2) ∧ p2) → True) ∧ p1) → p2) ∨ (p3 ∨ ((p2 ∨ p1) ∨ True))) ∨ (p2 → ((p1 ∧ p2) → (p1 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668684659059157694846170176269 : (((((((True ∧ (((p3 ∧ (p4 → (p1 ∧ p1))) ∧ (False ∧ p4)) ∨ ((p2 → p3) → p2))) ∨ p4) ∧ False) ∨ True) ∨ ((p5 ∨ p4) ∧ False)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_740483083330880455512586714424 : ((((p1 ∨ p5) ∨ ((((p3 ∨ ((p1 ∨ (p2 ∨ False)) ∨ True)) → (p2 ∨ p1)) ∨ (p3 ∧ (p3 → False))) ∧ (p1 → (p4 ∨ (p1 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67913454829185176195565646478 : ((p2 → ((((((True ∨ p1) → p2) ∧ (p5 ∧ (p5 ∨ True))) → True) ∧ False) ∨ ((p4 ∨ ((p3 ∧ p3) ∨ (p1 ∨ p3))) ∧ (False → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48055169691154863829281902114 : ((((p4 ∨ ((True → False) → (True → (False → p2)))) ∧ ((((p1 ∨ (p2 ∧ p3)) ∨ ((p5 → True) → p4)) ∨ p5) ∧ p1)) → (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309074983241836739165045084735 : (p2 ∨ ((p1 ∧ (p3 ∧ ((p3 → False) ∧ (((((p3 ∨ (p2 → p4)) → p3) ∨ (p2 ∧ p1)) → True) → (p5 → ((True → True) ∨ p1)))))) → p2)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53956026252533261410924951126 : (((((True → (p5 → (p4 ∧ (p4 → p1)))) ∧ p1) ∧ True) → ((p5 ∨ (False ∧ p5)) → ((((False → True) → False) ∧ p5) → (p3 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51614060920262407669986675183 : (((((p2 ∨ (p5 ∧ (((p1 ∨ True) ∧ ((False → p2) ∨ p2)) → p4))) → p2) ∧ p2) ∧ ((True ∨ ((p5 → p3) ∧ p2)) ∨ (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1493917625439820196309635922 : (((p5 ∨ (((p1 → (True ∨ True)) ∧ ((((p4 → (p4 → p3)) ∨ p5) ∧ (p2 ∨ p5)) → False)) → False)) ∨ (False → p5)) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65180051185690359726026037378 : ((p3 ∨ (((p1 ∨ (p2 ∨ p1)) ∧ ((((p1 ∧ p4) → p3) → (p1 ∨ ((p2 ∧ p5) ∧ p3))) ∧ ((p4 ∧ p5) ∨ (True → p5)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246204373304266183482037378646 : ((p4 ∧ p3) ∨ ((((((p4 → p1) ∨ ((p4 ∧ True) → True)) ∨ True) ∨ (((False → (p3 ∧ p5)) ∧ p2) ∨ (p5 → p5))) → False) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608783010209975123678885181305 : ((((((((p5 ∨ p4) ∨ False) ∨ (p4 ∨ (p3 ∨ (True ∧ (((True ∨ False) ∨ (p3 → False)) ∧ p5))))) ∨ (p5 ∧ (p3 ∨ p2))) ∨ True) ∨ False) ∨ False) ∧ True) := by
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
theorem thm_5_vars_677513465229028459708971087801 : ((((((True ∨ p3) → ((((True → p1) ∧ ((p4 ∧ (p4 ∧ p4)) → p2)) ∧ (p5 → p4)) → p2)) ∨ True) ∨ (((p3 → p3) → False) ∧ p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_186888796676470884229761183163 : (((True ∨ ((p2 → p5) ∨ p3)) → ((True ∨ (p3 → p5)) → False)) → (p1 ∨ ((False ∧ (((True ∨ p3) ∨ p3) ∨ (p5 ∨ p4))) ∧ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p2 → p5) ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p3 → p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249746892796447109603280793830 : ((p5 ∨ p5) ∨ ((False → (p1 ∧ True)) → (p5 → (((True ∧ (p3 ∧ p2)) ∧ p1) ∨ ((((True ∧ True) ∧ (p4 → (True → p5))) ∨ p1) ∨ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299180053266976581984524335536 : (False ∨ (((((((p5 → p2) ∧ (p1 → p2)) ∧ True) → False) ∧ (((p1 → False) ∨ ((p1 ∨ (p4 ∧ (p4 ∨ True))) → True)) ∨ p3)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147598172319509567120538286192 : (((((p3 ∧ (p3 → (((p2 ∨ ((False ∧ p1) → p3)) → True) ∧ p2))) ∧ (p1 → (p1 ∧ p1))) ∨ True) → p4) ∨ ((False → (True ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173354430063586066208992696990 : ((p3 → ((p3 → (((p3 ∨ False) ∨ ((p5 → True) ∨ p1)) ∧ p1)) ∧ (p5 ∨ True))) ∨ (p4 → (((True → False) ∧ (False → (True → True))) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232375007764694033965794012896 : (((p5 → True) → p4) → ((p1 ∨ (((p5 ∨ True) ∧ ((((p3 → p2) ∨ (p4 → p5)) ∨ (p5 ∧ p1)) ∧ False)) ∧ p5)) ∨ (p1 → (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185030694800448918798986612940 : (((True → p1) ∧ ((((p1 → p5) ∨ False) ∧ p3) ∨ (True → p3))) ∨ (((False → p1) ∨ (p3 → True)) ∧ (p4 → ((p2 → False) ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302058500093437882347826348838 : (False ∨ (True ∧ (p5 ∨ ((True ∧ (p2 ∨ (p4 ∧ False))) ∨ (((False ∨ (((p5 → (p3 ∨ False)) → False) ∨ (p3 ∨ p4))) ∧ (True ∨ True)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116167082240894909080058772024 : (((True → (p2 ∨ p2)) ∧ (((((p1 ∨ (((p2 ∧ p5) ∨ p5) ∨ True)) → (p2 → p5)) ∨ (False ∧ p5)) → (p3 ∧ p3)) ∨ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357424371930931370068379035638 : (p5 → ((p3 ∨ True) → ((((False ∧ (p1 ∨ ((p1 ∨ (p5 ∧ p3)) ∧ p3))) ∨ p2) ∧ ((p5 ∧ False) ∨ (p5 ∧ False))) ∨ ((p3 ∨ p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720938858946625244877169938783 : (((((p1 ∨ p1) ∧ (p3 → p4)) → (((p4 → ((False ∧ (False ∨ False)) ∧ ((((p4 → False) → p4) ∨ p1) ∨ p5))) → (False ∨ p2)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2571436008838280780751677517 : ((p5 → (((p3 ∧ (p1 → False)) ∨ p4) ∨ p3)) ∨ ((p4 ∨ (((p3 ∧ p3) ∨ p2) ∨ True)) ∨ (False ∧ (((p1 ∧ True) → p5) ∧ p2)))) := by
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
theorem thm_5_vars_225161983617577790500580686123 : (((p3 ∧ p5) ∧ True) ∨ ((p4 ∨ ((True ∧ p5) → ((((p3 ∧ (True ∧ p3)) ∨ p3) → ((False ∧ p1) ∨ (p4 ∧ (False ∨ p1)))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44695446445711573876183160558 : ((((((p4 ∨ p2) ∧ p5) ∨ p1) ∧ (((p4 ∨ p5) ∧ p3) ∨ (((((False ∨ p5) ∨ False) ∨ (p2 ∧ (p3 ∨ p5))) ∧ False) ∨ p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38249785365876215989708400011 : ((((((((p1 ∨ p1) → True) ∨ False) → (p2 → p4)) ∨ ((p2 ∧ False) ∧ ((True → p1) → p2))) ∧ (p3 → (p5 → (p3 → True)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308975691454781426104989147464 : (p2 ∨ ((((p4 ∨ p4) ∧ (True ∨ (p2 ∧ (True ∧ True)))) ∧ ((p5 → ((((p1 ∧ (p3 ∨ p3)) ∨ p3) ∧ False) ∧ (p2 ∨ p2))) ∧ p5)) → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h3.left
      let h24 := h3.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h25 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h26 := h23 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h3.left
      let h35 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h30



