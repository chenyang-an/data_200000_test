variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258859334822766007541256533039 : ((True → p1) → ((p2 → False) ∨ ((p5 ∧ (p4 ∧ ((True ∧ (p3 → (p2 → (p3 ∧ (False ∨ True))))) → p5))) ∨ (p4 → ((p4 → p5) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119135244968082318733254470518 : ((p1 → (p3 ∨ (((p3 ∧ ((p4 ∨ p4) ∧ ((p3 → False) ∧ True))) ∧ (((True → p4) → (p4 → False)) ∨ (True → p4))) ∨ p1))) ∨ (p3 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157424637952896067302454999216 : ((((p5 ∨ p5) ∧ (True ∧ ((p4 ∧ ((True ∨ (p2 ∨ p4)) → False)) ∧ (True ∧ True)))) ∧ (False ∨ True)) ∨ (p3 ∨ (((False ∧ p2) ∨ False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2094898935941266381135820282 : ((p1 ∧ (((False → True) ∨ ((p3 ∨ p1) ∧ True)) → (True → (p5 ∧ (p5 ∧ (True → True)))))) ∨ ((False → (True → p3)) ∧ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209163272680050510644951296048 : ((p3 ∨ (True ∨ ((p5 → p3) ∨ p4))) → ((p1 → ((p4 → p2) → (p3 → False))) ∨ ((True → (p2 → (True ∧ (True ∨ (p5 ∧ True))))) ∨ p5))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346315985457566827023565988643 : (p3 → (((p4 → ((p5 ∨ (False ∨ (p4 ∧ (((p5 ∨ True) ∧ p3) ∨ ((p5 ∨ (p1 ∨ False)) ∧ True))))) ∧ p4)) ∧ (p5 ∧ p5)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747472141815221997323207663689 : ((((True → False) → (p3 → (((True ∧ p3) ∧ p1) ∨ (p3 ∧ ((((p1 ∨ p3) ∧ (p5 → True)) → False) ∨ ((p4 ∧ p3) ∧ (p4 → True))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215780660131877263481711654351 : ((p1 ∨ (False ∧ (p1 ∧ p4))) ∨ (((p1 → (False ∧ (p4 → (p2 → (((p1 ∧ (p3 ∧ p4)) ∨ False) → ((False → False) ∨ p5)))))) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626121998515237743952900735835 : ((((p3 → ((((False → (p1 ∧ (True → ((True ∨ (False ∨ (p1 → ((p3 → p1) → (p4 ∨ True))))) → p1)))) → p5) ∨ True) ∧ p3)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_64496816456367503653122930119 : ((p1 ∨ ((((p2 → (p3 ∧ ((False ∨ ((p1 ∨ p5) → (False ∨ p1))) ∨ p5))) → p5) ∨ True) → (p2 ∧ (((False ∨ p5) ∨ p3) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165614388507441371085418332066 : (((p4 ∨ (True → (False ∧ ((p5 ∨ p2) ∧ True)))) → ((((p2 ∧ p5) ∨ p3) ∧ True) ∨ p4)) ∨ (((p4 ∨ p3) ∨ (True ∧ (p1 ∧ False))) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64484246086661194694391768277 : ((p1 ∨ ((p5 ∨ ((True → False) ∨ (p1 ∨ (((p4 ∨ (False ∨ (p2 ∨ p1))) → (p1 ∨ p1)) ∧ p3)))) ∨ (p3 ∧ ((True ∧ True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199153779572871166992507202851 : ((((p3 → p1) ∨ ((p4 ∧ False) ∧ p5)) ∧ p1) → ((((p1 → (False ∨ ((False ∧ (True → p3)) ∨ p1))) ∨ False) ∨ False) ∨ ((False ∧ True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326851321584491422045572725354 : (True → (((p5 ∧ (False ∨ ((p4 ∨ (p4 ∧ ((p4 ∧ p3) ∨ (p5 ∧ (((p4 → True) → ((p2 ∨ True) ∨ p1)) ∨ p3))))) ∨ p3))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171483325594305459758660034949 : (((True → ((True ∨ p2) → (p3 ∧ (((p1 ∧ (p2 ∨ False)) → False) → p1)))) ∧ True) ∨ (p3 → (p3 ∨ (((p2 ∧ (p5 → p5)) ∧ p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59259313072628720955401689520 : (((p2 ∨ p5) ∨ (True → (p4 ∨ ((((False ∧ p3) ∨ (((True → p5) ∧ p2) ∧ ((p2 ∧ (p3 ∨ p5)) ∧ p1))) ∨ (p2 ∧ p3)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46530008463374340675630486144 : ((((p4 ∧ True) ∨ (((p1 ∨ p2) ∨ p2) ∧ ((p3 ∧ (p5 ∨ ((p5 → False) → p3))) → ((p1 ∨ (p3 ∨ False)) ∨ p2)))) ∧ (p3 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246725831902220127910682590669 : ((p5 ∧ p4) ∨ (p5 ∨ ((p2 ∧ ((((p5 → (((p1 → ((p1 ∧ p4) ∨ p5)) ∧ (p5 ∧ p2)) → False)) → p4) ∧ (False → p2)) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317575393474724246022708489193 : (p4 ∨ (((((((p5 ∨ p1) ∨ p1) ∨ p1) ∨ (((p2 ∧ True) ∨ True) ∨ ((((p5 ∧ p5) ∧ p1) ∧ p1) → (p4 ∨ p5)))) ∧ True) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115078818060060247776143432212 : (((False ∧ (p5 ∨ ((((False → p4) ∧ (p3 ∧ p2)) ∧ p2) ∧ p3))) ∨ ((p3 ∨ p5) → (((False → p5) → p1) ∨ (True ∧ p5)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171520482997022809857491582588 : ((((p3 ∨ (True ∨ (((True ∧ p4) → ((p1 → p2) ∨ p1)) → p5))) ∧ p1) ∨ p4) ∨ (((p2 → p2) ∨ p2) → (p5 → (p5 → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779353759963817045337034360432 : (((p2 ∨ ((p5 → ((p1 ∧ ((((p2 → (False → (p4 ∨ p3))) → (p2 → False)) → False) ∨ (p5 ∧ ((p2 ∨ p1) ∧ False)))) → p2)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156897012023925212829883285999 : ((((p1 ∧ (((((True ∨ p3) ∨ p4) ∧ p3) ∨ (p4 → (p3 → p4))) → (p2 ∨ p3))) ∨ p3) ∨ p2) ∨ ((p1 ∧ True) → (True ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302907873054239758246385872397 : (False ∨ (True → (p4 ∨ ((((p1 → p4) ∧ True) ∧ (p1 ∧ (p3 ∧ p1))) → (p2 → (((False ∧ ((True ∨ False) ∨ p2)) ∧ (p4 ∧ False)) ∨ p3)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774545263888999956760587041708 : (((False ∨ ((((p1 → False) ∨ False) → ((((False ∧ True) ∨ False) ∨ (p2 ∨ p2)) ∨ p3)) → ((((p2 → p5) → (p3 ∧ p1)) ∨ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326278227305173861244231804412 : (p5 ∨ (p4 → ((p2 → (p4 → ((((p1 ∨ (True ∧ (p4 ∨ (p2 ∧ (p4 → p1))))) ∨ False) → False) → ((False ∨ True) ∧ (p3 ∨ False))))) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∨ (True ∧ (p4 ∨ (p2 ∧ (p4 → p1))))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60703197373619489679676868259 : ((True ∧ ((((True → p5) ∧ False) → (True ∧ (True ∨ p5))) ∧ (((p5 → ((p1 ∧ p5) ∨ ((p3 ∧ (p2 ∨ p5)) ∧ p2))) ∨ p2) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180853143892838241125745516548 : ((((p2 ∨ True) → p4) ∨ (((True → ((p5 ∧ p3) → p3)) ∧ p2) → True)) → (((((p5 → p1) ∧ ((False ∨ p2) ∨ p5)) ∨ p1) → p5) ∨ True)) := by
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
theorem thm_5_vars_171616913579725298139750440648 : ((((p2 ∨ ((p2 ∧ p1) → True)) → ((True ∧ p3) ∨ (p2 ∧ (p2 ∧ False)))) ∨ False) ∨ (p5 → (((p4 ∨ (p4 ∧ p2)) ∨ p2) ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113581724828293390894164101309 : (((p1 ∧ (p2 ∧ (((((False ∨ p1) ∨ p5) ∨ (p4 → p4)) ∨ (p3 → (False ∧ (p3 → False)))) → (p1 → p2)))) ∨ (True → p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52320122883874649139230773053 : (((((p5 ∧ ((p1 ∨ p3) ∨ (p1 → p2))) → ((True → False) → p4)) ∨ False) ∧ ((p1 ∨ p2) ∧ ((((p2 → p4) ∨ True) → p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189193977716288543061582306795 : (((p4 ∧ p5) ∨ ((p5 → True) ∨ ((p2 ∧ p3) → p4))) ∧ ((((p4 ∧ (p4 ∨ ((False ∨ (True ∧ p5)) → p5))) ∨ p5) ∧ (p2 ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788866691974085356204259227863 : (((p5 ∨ ((((p1 ∧ ((True ∨ (True → ((p4 ∧ (p3 ∧ p1)) ∨ p4))) ∨ p4)) → p3) ∧ (((p1 → p1) → p2) ∧ p1)) ∧ (False → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157512283481637808709222022045 : (((p5 ∧ ((p2 ∧ (((p2 ∧ (p5 ∧ (p3 ∨ False))) ∨ p2) ∨ False)) ∧ (p3 ∧ p1))) ∨ (p1 ∧ p1)) ∨ ((False → (p4 → p4)) ∧ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137784177573269981122465227523 : ((p2 ∨ ((p3 → (False ∧ p4)) → ((((p1 ∧ (p3 → True)) → ((p3 → False) ∧ (p5 → p2))) ∧ (p5 ∧ p3)) ∧ p5))) ∨ ((p2 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134624504132587767721229998599 : ((((p2 ∨ (((p3 ∧ p2) ∧ (((p2 ∨ True) ∧ (True ∧ (p1 ∨ p5))) ∨ p4)) → p1)) → ((False → p3) ∧ p4)) → p4) ∨ (True ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167556169220941713545422659418 : ((((p3 ∨ ((((p1 ∨ p2) ∧ True) ∧ (p4 ∨ True)) ∨ (p2 ∧ p4))) ∨ True) ∨ (p5 → p4)) → (False ∨ (False → (((p2 → p1) ∧ p2) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- False on the left can always be used.
        apply False.elim h5
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h17
              -- Implications on the right can always be decomposed.
              intro h18
              -- Conjunctions on the left can always be decomposed.
              let h19 := h18.left
              let h20 := h18.right
              -- False on the left can always be used.
              apply False.elim h17
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h22
              -- Implications on the right can always be decomposed.
              intro h23
              -- Conjunctions on the left can always be decomposed.
              let h24 := h23.left
              let h25 := h23.right
              -- False on the left can always be used.
              apply False.elim h22
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h28
              -- Implications on the right can always be decomposed.
              intro h29
              -- Conjunctions on the left can always be decomposed.
              let h30 := h29.left
              let h31 := h29.right
              -- False on the left can always be used.
              apply False.elim h28
            case inr h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h33
              -- Implications on the right can always be decomposed.
              intro h34
              -- Conjunctions on the left can always be decomposed.
              let h35 := h34.left
              let h36 := h34.right
              -- False on the left can always be used.
              apply False.elim h33
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- Implications on the right can always be decomposed.
          intro h41
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- False on the left can always be used.
          apply False.elim h40
    case inr h44 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h45
      -- Implications on the right can always be decomposed.
      intro h46
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- False on the left can always be used.
      apply False.elim h45
  case inr h49 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h50
    -- Implications on the right can always be decomposed.
    intro h51
    -- Conjunctions on the left can always be decomposed.
    let h52 := h51.left
    let h53 := h51.right
    -- False on the left can always be used.
    apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168585390378692248257024528107 : ((p2 ∧ (((False → False) ∨ p5) → (p2 ∨ (((p5 → p2) ∧ ((p1 → False) ∧ p4)) ∧ p2)))) → ((False ∨ p3) → (p3 → ((p1 → p5) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669597641487785445006760712090 : (((((True → ((False ∧ (p3 ∨ (((p3 ∧ p1) → (False → (p1 ∧ p1))) → p5))) ∨ p1)) ∧ ((False → p5) → p1)) ∨ ((p1 ∧ p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314554189353002147529925071599 : (p3 ∨ (((p2 ∧ False) ∧ ((p1 ∨ True) → (p3 ∨ (((False ∧ p1) ∨ False) → (p5 → (p5 ∨ True)))))) ∨ (p4 ∨ (p5 → (p3 ∨ (p5 ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342750601292360470743642529568 : (p2 → ((((p5 ∨ True) ∨ (True → (True ∨ p5))) → False) ∨ (p5 → ((p2 → True) ∨ ((p1 ∧ (((p5 ∨ p3) ∨ p4) ∧ (p4 ∨ False))) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117213085304616510761822188775 : ((True ∧ (((False ∨ False) → (p3 ∨ p3)) → (((p5 ∧ (p5 ∨ ((p2 ∧ (p1 → ((p1 ∨ p3) → False))) ∨ p1))) ∧ False) ∨ True))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18015869530505297341035974906 : ((((p3 ∧ p2) ∧ (((True ∨ (p1 ∧ False)) ∧ p1) ∧ (((p2 ∧ (p3 ∨ p4)) ∨ True) ∨ (p1 ∨ True)))) ∨ (((p3 → p1) → p1) → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149247616068743359037992285927 : (((p1 ∨ p3) ∨ (p1 ∧ ((((p2 → (False ∧ ((p5 ∨ p1) ∨ p4))) → p1) ∧ p2) ∨ (p4 → (p1 → p2))))) ∨ ((p1 → p2) → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327109946249349270800904555374 : (True → (((p2 ∨ p3) ∨ ((True → (False ∨ ((((p2 → (p3 ∨ (p4 ∨ p5))) ∧ p4) ∧ p5) → (((True → False) ∧ p4) ∨ p4)))) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199631492091350011694853566707 : (((((p4 ∧ p5) ∨ p5) ∨ (True ∨ p2)) → False) → (((p1 → (((False → p5) ∧ (False → ((p2 ∨ (True ∨ False)) → True))) → p2)) ∨ p3) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ p5) ∨ p5) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178468242508416293239237465164 : ((((((p2 → (p3 → p5)) → False) ∧ True) ∧ True) ∨ (p2 ∨ (True → True))) ∨ ((((p3 ∧ (p5 ∨ (p2 ∨ (p4 ∨ False)))) ∨ False) ∨ p4) ∧ p3)) := by
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
theorem thm_5_vars_118328366839219541190198797461 : ((p2 ∨ ((((((((p2 ∨ (False ∧ p1)) ∧ (p1 → (p5 → p4))) → p4) → False) → p2) ∨ True) ∨ (False ∧ (p2 ∧ p1))) ∧ p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136675926867379978596570606822 : (((p5 ∨ (p5 → p3)) → ((p5 ∨ (((p2 → p4) → p1) → p4)) ∨ (p1 → ((p5 → p1) ∨ (True → (False ∨ p5)))))) ∨ ((p2 → p3) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197537057075775699822276411376 : (((((p5 ∨ p1) ∧ p4) ∨ p1) ∨ (True → p4)) ∨ ((((True ∧ True) → p3) → True) ∨ (False → (True → (((p1 ∧ p2) ∨ p4) ∨ (p2 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68362583913641911695983998304 : ((p3 → ((p4 ∨ ((((p4 ∧ False) ∨ p3) → p4) ∨ p4)) → (((p2 ∨ p5) ∧ ((True ∨ (p3 → False)) → p3)) ∨ (True ∨ (p5 ∧ p4))))) ∨ p4) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157515616087006272067947605555 : (((p1 ∨ ((p1 ∨ (p1 ∧ ((p2 ∧ True) ∧ p3))) ∧ ((True ∧ (p5 ∧ p3)) → p2))) ∨ (p2 → p5)) ∨ (((False → False) → True) ∧ (False → False))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152849840984814411214418194604 : (((p3 → True) → (((False ∨ p5) ∧ (((((False → p2) ∧ (p4 ∨ p2)) ∧ False) ∧ (p5 ∨ p3)) ∧ False)) ∧ p2)) → ((p3 → p3) → (False ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38381549761572769340934933721 : ((((((((p1 ∨ (p1 ∧ p3)) → (p3 → p5)) ∨ ((p1 ∧ False) → False)) ∨ p3) ∨ p5) → (False ∧ ((p1 → (True ∨ p5)) ∨ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42051035963411339555642715501 : ((((p1 ∨ p1) ∨ (False ∧ ((p4 → p5) ∨ (False ∨ (p3 ∨ (p4 → (((p4 → (p3 ∧ True)) → p2) ∨ (True ∧ (p5 → True))))))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37296628282099172439149294934 : ((((True → ((((p1 ∨ (p5 → False)) ∧ False) → ((((p5 ∧ True) → (p5 ∨ ((True → True) → p1))) → p5) ∧ True)) → p4)) ∧ p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115902039315649558901266955107 : ((((p3 ∧ (p4 ∧ True)) → False) ∨ (True ∧ (p2 → ((p3 ∨ True) → ((((True → p2) → (p4 ∧ (p2 ∧ True))) ∨ p4) → p3))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41141541724810801403201402014 : ((((((((True → True) ∧ (p2 ∨ p3)) → (True ∧ (p3 → p2))) ∧ p2) ∧ ((True ∨ (p4 ∨ p1)) ∧ p2)) ∨ (p2 ∨ (p4 → p1))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48340199184526920712275917963 : (((p2 ∨ (p2 ∧ ((p2 → p5) ∨ (((True ∧ (((((False ∨ p4) → (True → p5)) ∨ p3) ∨ p2) ∨ True)) ∨ True) ∧ p4)))) → (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58994658623391465871991320623 : (((p3 ∧ False) ∨ (p1 ∨ (p3 → (p4 → (True → (((False ∨ p5) ∨ True) ∧ (((((p1 ∨ False) ∧ False) ∧ (p2 ∧ False)) ∧ p5) → p1))))))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250040301059648698043582983438 : ((True → p3) ∨ (((True ∨ (((p5 → p2) ∨ (p5 → (p4 ∧ p4))) ∧ p1)) ∧ (p3 → p1)) → (p5 → (((p2 ∨ p5) ∨ p2) ∨ (p3 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137960944900429219520905487310 : ((p5 ∨ ((p3 → (True ∧ (p5 ∧ (p4 → (((p2 ∨ p2) → (True ∧ ((False ∧ True) ∨ False))) ∧ p2))))) ∧ (True ∨ p2))) ∨ ((True → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253978712829978396504209945604 : ((p1 ∧ p5) → ((False ∨ ((((p3 → True) ∧ (p4 → p3)) → p2) ∨ ((p1 ∨ (True ∨ (p5 ∧ (p5 ∨ p2)))) ∧ (False ∧ p1)))) ∨ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602014777873702963094940645422 : ((((p5 ∧ (((True ∨ (False → (((p3 ∧ p5) ∨ (p4 ∧ False)) ∨ ((False → p2) ∧ (((True → p4) → False) → p1))))) → p5) ∨ p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191896223584008134163872507832 : ((p5 ∨ (((False ∨ ((p1 ∧ False) → False)) ∨ p4) → p4)) ∨ ((p1 ∧ (p5 ∨ p2)) ∨ ((p2 ∧ p2) → (p4 ∨ ((p3 ∧ (p3 ∧ False)) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164939197022315143026215553803 : ((((p4 → (p2 → (((p4 ∨ p5) → (((False ∨ p1) ∧ p5) → p3)) ∧ p2))) ∨ p3) → p1) ∨ (True ∨ (False ∨ ((p2 ∧ (p2 ∨ True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164767830922690994477089885314 : ((((((p1 ∨ ((True ∧ p4) → p1)) → p3) → False) ∧ ((p3 → p5) ∨ (False ∧ p5))) ∨ p1) ∨ (True ∨ (True → (True ∧ (False ∧ (p2 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630182937604516757441979365759 : ((((((False ∨ p5) ∨ (True → ((True ∧ (((((p1 ∧ p3) ∨ True) → p5) ∨ (p4 ∨ p1)) ∧ (p2 → (p2 ∧ p2)))) ∨ p5))) ∨ False) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103234887415987527686039923071 : (((p3 ∧ (((True → ((p1 → (p3 → (p2 ∨ p3))) ∧ ((True ∧ True) ∨ p5))) → ((p4 ∧ p4) → (p2 ∨ False))) ∧ True)) ∨ True) ∧ (p2 → p2)) := by
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
theorem thm_5_vars_40938888648993094749232709729 : (((((p2 ∨ ((p4 ∧ ((p4 ∧ (p1 ∧ (p4 ∧ (True ∧ True)))) ∧ ((True ∨ (p2 ∧ p5)) → False))) ∨ p5)) ∨ p1) ∨ (False → p2)) ∨ p2) ∨ p3) := by
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
theorem thm_5_vars_727493920397329502006303926373 : ((((p4 ∧ (False ∧ True)) ∨ (((p2 → (((p2 → (((p3 ∧ p1) ∧ ((False → (p1 ∨ p2)) ∧ p2)) → p2)) ∨ p5) → p3)) → p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709002064730775948252277309033 : (((((p5 ∨ (p3 ∨ (False → p2))) → (True ∨ p4)) → ((((True → p2) ∨ True) ∨ p4) ∧ (((True ∨ p5) → p1) → (p2 ∨ (p2 ∨ True))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52657933623647270020226227711 : (((p2 ∧ (p2 ∨ ((False ∧ p1) ∨ (True → (((p3 ∧ p5) ∨ p4) → True))))) ∨ (((p2 ∨ False) ∨ (p2 → True)) ∧ ((p2 → p3) → True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39633425844006704469114950763 : (((p3 ∨ (((p1 ∧ ((p2 ∧ False) → ((p4 ∨ p5) ∧ ((p2 ∨ p1) ∧ p2)))) ∨ (p4 ∨ (((False ∨ p5) ∨ True) ∧ p1))) ∨ False)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42027816149384081115582322042 : ((((p2 ∧ True) ∨ (((p5 ∨ p1) → (True → (p3 → (p2 ∧ (p2 ∧ p3))))) → ((((False ∨ p2) ∧ p3) ∨ (p3 → True)) ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136657209724810578590379772214 : (((p2 ∧ (p1 ∨ p4)) → ((p3 ∨ p1) ∧ (False ∧ (p2 → (p2 ∧ ((p5 ∧ (p5 ∨ ((p1 ∨ p1) ∧ False))) → p1)))))) ∨ (p2 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187171253815206964948892492268 : (((False ∧ p2) → ((p3 ∨ (p2 → p4)) ∨ (True ∧ (p2 → p3)))) → ((p3 → p4) ∨ ((((p4 → (True ∨ p3)) ∧ (False ∨ False)) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41679541426147098895715206612 : (((((p3 → p5) ∨ ((p5 ∧ p4) → p1)) ∨ (((p2 ∨ p2) ∧ (False ∨ (p3 → (p2 ∨ (False → (True ∨ (p5 ∨ True))))))) ∨ p1)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147342343449028700346953449628 : ((((((False ∧ (p1 ∧ (True ∧ ((True ∧ (p2 ∨ p3)) ∧ False)))) ∨ p5) ∨ (p1 → p5)) → (p4 → p2)) ∨ p5) ∨ ((p1 ∨ True) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591161093824618521313444175939 : ((((((p2 ∧ (p4 → (p3 ∧ (p4 ∧ ((((p4 ∨ p5) ∨ True) ∧ p3) → (((p2 ∨ True) ∧ p1) → p5)))))) ∨ True) ∧ (p2 ∨ p4)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180814885986205915632481635304 : ((((False → p5) → False) ∧ (((p3 → ((p4 ∨ True) ∧ p1)) → p4) → True)) → (p4 ∧ (p4 ∧ (((p1 → (False ∨ True)) ∨ p5) ∧ (p3 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h14
  -- False on the left can always be used.
  apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h19 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h21 := h17 h19
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137058759912585388894484057289 : (((p2 → p2) → (((False → (p3 ∨ p5)) → ((True ∧ (False ∧ p5)) ∧ ((False ∨ p1) → (p4 ∨ (p3 → p4))))) ∨ p3)) ∨ (p4 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219045214445573528167537275994 : ((p5 ∧ ((True ∨ p3) → p3)) → (p3 ∧ (p2 ∨ (((p5 → p2) → (((False ∨ (p4 ∨ (p3 → p4))) ∨ ((True → p3) ∨ p3)) → p2)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h17 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h18 := h8 h17
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h22 := h8 h21
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h24 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h25 := h8 h24
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165648290517868089694998800397 : ((((True → (True → (True ∧ False))) ∧ p5) ∨ (p3 → (((False ∧ True) ∧ (p2 → p4)) ∧ p2))) ∨ (((p2 ∨ (p3 → p4)) ∧ True) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949882728299329988256442644925 : (((((False ∧ True) → p5) ∧ (p5 ∧ ((((((p1 → ((p2 → False) → p3)) → p2) ∨ (False → True)) ∨ p3) ∨ (True ∧ p1)) → (p4 ∧ p3)))) → p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596743158193182471511228686197 : (((((p5 ∧ (p5 ∨ (p3 → (p4 → False)))) ∧ ((((p3 ∨ (False ∧ (True → (False → (p3 ∧ False))))) ∧ (p2 ∧ p2)) → False) → p3)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315008762330389000340145436371 : (p3 ∨ ((((p4 → p1) ∨ ((p3 → p2) → p4)) ∨ p3) ∨ (True ∨ ((p1 ∧ (p4 ∧ p5)) → (p2 ∨ (p4 ∨ (((p2 → p1) → p4) ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257023801841061988274639748809 : ((p2 ∨ True) → ((((p4 ∨ ((p3 → (True ∧ p3)) ∧ False)) ∨ p2) ∨ (False → (p3 → p4))) ∨ ((p2 → p1) → (True ∧ ((False → p2) ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111224988571852918606649613264 : ((((p3 → (p5 → p2)) → ((p1 ∨ p1) → (((p2 ∨ (p1 ∨ p1)) ∧ (p1 ∨ p1)) ∨ ((p1 ∧ p3) → (p1 → True))))) ∧ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594516170363868334960503887776 : (((((((p1 ∨ (False → p5)) ∧ (p4 ∨ (p1 ∧ p1))) ∧ ((p4 ∨ (False → p2)) ∨ p5)) ∨ (((p1 ∨ p2) ∨ p5) ∨ (p2 ∨ p2))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185034781943276755668456414768 : (((False → p3) ∧ ((p2 ∨ (p4 ∧ (p2 → p1))) ∧ (p2 ∨ True))) ∨ ((((p1 ∧ p3) → (((True ∨ p2) → p5) → p5)) ∨ (False → p2)) ∨ p1)) := by
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
theorem thm_5_vars_762401842225317727169447782589 : (((p3 ∧ (((p2 ∧ p4) → ((((p3 ∧ p3) → (False ∨ (p1 ∨ p1))) → p4) ∧ (((False ∧ p2) ∧ p1) ∨ p3))) → ((True ∧ p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700989552821949096473197631929 : (((((p4 ∨ ((p1 ∨ (True ∨ (p3 → p1))) ∧ p4)) ∨ True) ∧ (((p3 ∨ (p5 → p2)) → (((p2 ∧ False) ∧ (p5 ∨ p2)) ∨ p1)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165503049107475375400948451502 : (((p2 → ((p2 → p2) ∧ (p5 ∧ ((p3 → p1) ∨ p3)))) ∨ (p2 ∧ ((p4 → p1) → p4))) ∨ (True → ((p3 ∨ True) ∧ (False → (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127321323785973981591194779481 : ((p2 ∨ ((p1 ∧ (p2 ∨ (False → p5))) → (p3 ∧ ((p2 → p1) ∨ ((p1 ∧ (p3 ∧ (True ∧ (p1 → (p1 ∧ p1))))) → False))))) → (p3 → p3)) := by
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
theorem thm_5_vars_340696103847123318645873665461 : (p2 → ((((((True ∨ (p5 ∧ p4)) → ((p3 → p2) → ((p2 ∨ p2) ∧ ((p4 ∧ p4) → (True ∧ (p4 ∨ p3)))))) ∧ p4) → False) ∧ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247574277303540509796459082776 : ((False ∨ p4) ∨ (p2 ∨ (p3 → (((((p5 → p3) ∧ p1) ∧ p4) ∨ (((False → False) ∨ (p2 ∧ True)) → (((False → p5) ∨ p4) ∧ True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317896273081827808058775176554 : (p4 ∨ ((p1 ∧ (False ∨ ((p2 ∨ True) → ((p1 → p2) ∨ (((p2 ∧ ((p3 → True) ∧ (((p1 ∨ p5) ∨ p5) → p5))) ∧ p2) ∧ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118259305765181453308475385611 : ((p1 ∨ ((((False ∧ (p3 ∨ p2)) ∧ p1) ∨ (((p3 ∨ True) ∨ (p3 → p5)) ∨ True)) ∨ (p2 ∨ (p2 ∧ (p3 → (True ∧ False)))))) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_44149539729104642631122809380 : ((((((p2 → p5) ∧ (((p4 ∨ (p2 → ((p5 → p5) → p5))) ∨ p5) ∧ (p3 ∧ (p1 ∨ p2)))) ∨ p5) → (True ∨ (p1 ∨ p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



