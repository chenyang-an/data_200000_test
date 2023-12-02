variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319291785901690601095091577214 : (p4 ∨ ((p2 → (((p5 → (True → p2)) ∧ False) ∨ ((p5 ∧ True) ∧ ((p3 → p5) ∧ p4)))) ∨ ((((p1 → p1) ∨ (p3 ∨ p3)) ∨ p5) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200994983428996450629249954815 : ((p3 ∨ ((p2 ∧ (p1 ∧ p5)) ∧ (p4 ∨ False))) → (True → (((p4 ∨ p1) ∨ ((False ∧ (p1 → ((p5 ∧ p4) → False))) ∧ (False ∧ p5))) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780843289552667323310583725211 : (((p2 ∨ (((p2 ∧ (True → p5)) ∨ p2) → (p3 ∨ (((p5 → ((p5 ∧ (p5 ∨ (p1 ∨ False))) ∧ (p3 ∨ p2))) ∨ True) ∨ (True ∨ p2))))) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
theorem thm_5_vars_652623563906519853039066887380 : ((((False ∨ (False ∨ (p1 ∨ (p4 ∨ ((False ∧ (((True → p4) ∧ False) ∧ (True ∧ ((p5 → p1) ∧ (p5 ∧ p1))))) ∨ p3))))) ∧ (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157831811326509802037624331717 : (((p1 ∨ ((p5 ∧ (p5 → ((p4 → p2) → p3))) → (p1 → p5))) → ((True → (p2 ∧ p1)) ∨ p4)) ∨ (((True → (True ∧ p4)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138379229755178288181902360777 : ((p4 → ((True → (False ∧ False)) → (((((True → True) → True) → p2) ∧ False) ∨ ((False ∨ (p5 ∨ p1)) ∧ (False ∨ p2))))) ∨ (p4 → (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78824545475187310611561224269 : ((((True ∨ ((False ∨ p1) → False)) → (False ∨ (p3 → (((True ∨ p5) ∧ p4) ∧ (((p2 → True) ∧ p3) ∧ (True → False)))))) ∧ (p3 ∧ p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ ((False ∨ p1) → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3920369496042691244698819122 : (False ∨ ((((p4 ∨ p1) ∧ p2) ∧ (((True → p2) ∧ (True ∧ ((p5 ∨ p4) ∧ (p1 ∧ p1)))) ∧ True)) ∨ (True ∧ (True ∨ (False ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55306307359043005777581129074 : (((p5 ∧ (p4 → ((p3 ∨ p4) → p5))) ∨ (p3 ∧ ((((p4 → False) ∨ (p3 ∧ ((False → p4) → p5))) → False) ∧ ((True ∨ True) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217115122493272390934488044109 : ((((p1 ∨ p4) ∨ True) ∨ p2) → (((False ∧ p2) ∧ p4) ∨ ((False → ((((True ∨ (True ∨ False)) → p2) ∧ p4) ∨ (False ∨ False))) ∨ (p3 → p5)))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h5
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962566358276186541182820538303 : ((((True → p4) ∧ (((p4 ∧ ((p1 → (p5 ∨ p5)) ∨ (((p2 ∧ p5) → p4) → p3))) ∧ True) → (((p3 → p4) ∨ True) → (p5 ∧ False)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136764436920874345611166125651 : (((p4 ∨ False) ∧ (((p2 ∧ True) ∨ ((p3 ∨ (p1 → ((p1 ∨ p3) ∧ p2))) ∨ p1)) ∧ ((p5 ∨ (False ∧ p5)) → p1))) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324961091162424844832220745966 : (p5 ∨ ((p5 ∨ p5) ∨ (((p5 ∧ ((p2 → p2) ∧ ((True → p5) ∨ p2))) ∨ (True ∨ p2)) ∧ (((False → p5) ∨ p4) ∧ (True ∧ (p1 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698825864949003520268578588284 : ((((True ∧ (((((False → p4) → p5) → (p2 ∧ True)) → p5) ∧ p1)) ∨ ((((p3 → p5) ∨ False) ∨ ((p2 ∧ (p3 → p5)) ∧ p4)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_702663955222118803435224673453 : ((((((p1 ∧ False) ∧ ((p4 → p2) ∧ p4)) ∧ (p2 ∧ p2)) ∨ (((((p4 ∨ p1) ∧ p2) ∧ ((p1 → (p4 → p2)) ∧ p1)) ∨ True) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230523443417777416206266760997 : (((False → True) ∧ p2) → ((((p5 ∨ (p1 ∨ ((p2 → p4) ∧ (True ∧ (False ∧ p5))))) ∧ p1) ∨ True) ∨ (((False → p5) → (p2 → False)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61685282145288770564753373657 : ((p1 ∧ (False ∨ (((((p4 → p5) ∧ p4) ∧ p2) ∨ p5) ∨ ((p2 ∧ p2) → (True ∧ ((((p2 ∧ (p1 ∧ p4)) → p5) ∨ False) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324368432305041522161568150556 : (p5 ∨ ((((True ∨ p5) ∧ p5) → (p4 ∨ p4)) ∨ ((((p1 ∨ p3) ∨ False) ∧ (p5 ∧ (((p4 ∨ True) ∧ (p2 ∧ False)) ∨ (False ∧ p4)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178070597216709820122307318010 : ((((p2 ∧ ((p1 ∨ p3) ∧ (True → (p1 → (p2 → p1))))) ∨ p5) → False) ∨ (((p3 → (True → p3)) ∨ (p2 → (p5 ∧ (p1 ∧ p1)))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763568644607668047342436106137 : (((p3 ∧ (p3 ∧ (p5 ∨ (p3 ∨ (((p2 → ((True → (p2 ∨ p5)) ∧ (p3 ∧ True))) ∨ (True → (((False → True) → False) ∨ p1))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193238273857413763864408493387 : ((((p1 ∧ p4) → False) ∧ (p3 ∨ (p3 ∧ (p1 ∧ p2)))) → ((p1 → (((p5 ∨ ((p5 ∧ True) ∧ False)) ∧ p5) ∨ (p4 ∧ (False → p2)))) ∨ p3)) := by
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
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150071393763837850727412170915 : ((True → (((p2 → p4) → (True → p1)) ∧ (((False → p2) → ((((p2 ∧ p4) → p1) ∨ p2) ∨ p3)) → False))) ∨ (False → ((p3 ∨ p4) ∧ p5))) := by
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
theorem thm_5_vars_192648764534587658511609960689 : ((((p3 ∨ ((False → False) ∨ (p3 → p2))) ∨ p1) → p4) → (((p5 → ((p2 ∨ p5) → p1)) ∨ (((True → p1) → (p1 → p4)) ∧ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ ((False → False) ∨ (p3 → p2))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219687683115185794292326501162 : ((p1 → ((p5 ∨ p4) ∧ p4)) → (((p1 → p4) ∨ (p4 ∧ p5)) → ((((p1 ∨ p3) ∨ (p4 → ((p5 ∧ p4) ∧ True))) ∨ True) ∨ (p3 ∨ False)))) := by
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
theorem thm_5_vars_40325618137491697683503325241 : ((((((((p3 ∧ (((p3 → (p3 ∧ (p2 → p3))) ∨ (False ∨ (p1 ∧ False))) → (p4 → False))) ∨ True) ∨ False) ∨ False) ∨ p2) ∨ True) ∨ p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806976945245191364762166113793 : (((p4 → ((((p5 ∧ ((((p4 → p4) → p4) ∧ (p5 ∨ p3)) ∧ (p2 ∧ (p5 → False)))) ∧ p1) ∧ (True → True)) ∨ ((False ∨ p2) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206903898755898306033277896777 : (((((p4 ∨ p1) ∨ p3) ∨ p1) ∧ p4) → (((True → p4) → ((True → True) → True)) → ((True ∨ ((p1 → p2) ∧ (p5 ∧ False))) ∧ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62033187494095965472992033626 : ((p2 ∧ ((True ∨ p2) ∧ ((((p4 ∧ p5) → p5) ∧ ((p3 ∨ (False ∧ ((p4 ∧ ((p5 → p4) → p3)) → p5))) ∧ (p2 ∧ p1))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737817090804462418072136957108 : ((((True ∧ False) ∨ ((False ∨ p5) ∨ ((p5 ∧ (((p4 ∨ (((p5 → (p2 ∧ True)) → p3) ∨ (True → False))) → (p4 → p2)) → p5)) ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173087291272358180116699681208 : ((p1 ∨ ((p2 ∧ ((p4 ∧ ((True → p2) ∧ p5)) ∧ p1)) ∨ (True ∨ (p1 → False)))) ∨ ((((p1 → (True → (p5 ∧ False))) ∧ p4) → p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51449798029928191990179003011 : (((((p3 ∧ ((((p3 → False) ∧ p5) → (p3 ∧ p5)) → False)) → p3) ∨ (p1 ∧ (False → False))) → ((False → ((p2 → True) → p1)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221282329355552304405167345517 : (((p3 ∨ p1) ∨ True) ∧ (((p5 ∨ (p4 ∨ (p3 ∨ True))) ∨ p2) ∨ (p1 → ((True ∧ (False → ((p1 ∨ p3) → (p2 → p4)))) ∨ (True ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644680368617268166676923866450 : ((((p1 ∨ (p2 ∧ (((p4 → p4) ∨ (p3 ∨ (p4 → (p5 → (p5 ∧ (p4 → (p5 ∧ p5))))))) ∨ (True → ((True ∨ p1) ∨ False))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62939823474894884485205909069 : ((p4 ∧ (p3 ∧ (p1 ∨ (p2 ∧ (True ∧ (False ∧ (((True ∧ ((p4 ∧ p5) ∨ True)) → (False ∨ p5)) → ((p4 → (False ∧ p1)) ∨ False)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177638950241325066023433779077 : ((((True ∧ (((False ∧ (p1 ∨ (p1 ∧ p5))) ∨ p3) ∨ p2)) ∧ p3) ∧ p2) ∨ ((((p2 ∧ True) ∨ ((p3 → True) ∧ (True ∨ False))) ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173326789779276130801313198974 : ((p2 → ((p1 ∨ (((p4 ∧ p5) ∧ (p2 ∨ False)) ∧ p5)) ∧ ((False ∧ p5) → False))) ∨ ((p5 ∨ True) ∨ (False ∧ (p1 → (p5 → (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52324852236771078125895342861 : (((((p4 → p5) → ((p2 ∨ p2) → (False → (p5 ∧ (p4 ∧ p5))))) ∨ p2) ∧ ((((p4 ∧ (p3 → (False ∧ p4))) ∨ True) ∨ p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167322581387222569565035804714 : ((((True → (((p2 ∧ p1) ∧ (p1 ∨ p5)) → (True ∨ (p3 ∧ p5)))) ∧ (p1 ∧ p5)) → True) → (((False → p4) ∧ p2) → (p4 → (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708762590068371218710502591370 : (((((False ∧ ((p1 ∨ p4) ∧ (p5 ∨ p2))) → p5) → (True ∧ ((p2 ∧ ((p5 → (p2 ∧ p3)) ∨ p2)) ∧ (False ∧ ((p5 → p2) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225430873271804330458978798769 : (((p3 ∨ p3) ∧ p4) ∨ (p5 ∨ (p4 → ((p3 ∨ (p4 ∧ (p3 ∨ (True → (p2 ∨ p1))))) → ((p2 ∨ ((True ∧ p4) ∨ True)) ∨ (p2 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748304421968144394627105580728 : ((((p2 → p1) → ((((p4 ∧ (p1 → ((((True ∨ p2) ∨ p5) ∧ p5) ∨ ((p1 ∧ p3) → (p2 ∨ (p5 ∨ p3)))))) ∨ p3) → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38706362771489117422334014877 : ((((p1 ∧ (p1 → (False → (p4 ∧ p1)))) ∨ ((p3 → p2) ∨ (((False ∨ ((p3 → ((p5 ∧ False) ∨ p3)) ∨ p2)) ∧ p1) ∨ True))) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138336471084503854766331770126 : ((p3 → (p5 → ((True ∧ ((p5 → False) ∧ (((p4 → (p5 ∧ (p4 → (True ∧ p5)))) ∨ False) → (False ∧ True)))) ∧ False))) ∨ (p2 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40436725766077768593792950455 : ((((((p2 → ((True → p2) → ((p4 ∧ p2) → False))) → p3) → (p5 ∧ ((p3 ∨ (p4 ∧ ((True ∧ True) ∨ False))) → p3))) ∨ True) ∨ p3) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329133845942241652381437171610 : (True → ((p3 ∨ ((p5 ∨ True) ∧ p1)) ∨ ((((p1 → p3) ∧ p2) ∧ (((False → p2) ∨ ((p3 → p3) ∨ p5)) ∧ (True → (p4 ∧ p1)))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h20 := h8 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134985205423011085190098879997 : ((((False ∧ p5) ∨ (((p5 ∨ (p3 ∨ p4)) ∧ ((True ∧ p2) ∨ (p4 ∧ (p4 ∧ p2)))) ∧ (p5 ∨ True))) ∧ (False ∨ p1)) ∨ (p3 → (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710446525911353198295558451543 : ((((((p3 → True) → (True ∧ p5)) → p5) ∧ (p5 → ((p1 ∨ p4) → ((((False ∧ ((p3 ∧ True) → p4)) ∨ True) → (False ∧ p1)) → p4)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∧ ((p3 ∧ True) → p4)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589311309985214012936581451596 : ((((((p1 → (((p4 ∨ (True → ((True ∧ ((p2 ∨ p3) ∨ p1)) → p4))) ∧ p4) ∧ ((p1 ∨ p4) ∨ (p5 ∨ p2)))) ∧ p3) → p5) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41287415285855345933559037104 : ((((((((p2 ∧ p5) ∧ p1) ∨ (p5 → True)) → p5) ∧ (True ∨ (p3 ∨ (True → (False ∨ p2))))) → ((p5 → p5) ∧ (p3 → p5))) ∨ p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h13 : (((p2 ∧ p5) ∧ p1) ∨ (p5 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h15 := h10 h13
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h18 : (((p2 ∧ p5) ∧ p1) ∨ (p5 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h18
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h22 : (((p2 ∧ p5) ∧ p1) ∨ (p5 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h24 := h10 h22
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53621217968983382963749009975 : ((((False ∨ (((p5 ∧ p3) → False) ∧ True)) → (p1 ∨ p1)) ∧ (True ∧ ((((False → p3) ∧ p1) ∧ ((p5 ∨ False) → p1)) ∧ (True → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116888466566518534937568784930 : (((p3 → p5) ∨ (((((p3 → False) → (p1 → p3)) → (p4 ∧ (p5 → p4))) ∧ ((p3 ∨ (p5 ∧ p4)) ∧ (p2 ∨ False))) ∨ p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188428313428856813965926183803 : (((((False ∨ p5) ∧ p2) ∨ ((p4 ∨ p1) ∨ p5)) → True) ∧ ((p4 ∨ (p5 ∧ ((p1 ∧ p2) ∧ p3))) ∨ ((p3 → True) ∧ ((p1 ∧ False) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98825725629848536736052536203 : ((True → ((False ∨ ((True → p2) ∨ (((((True → (p4 → True)) ∨ ((True → p1) → p3)) ∧ p5) ∧ (p2 → (p2 → p1))) → False))) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247430028448679557875077945949 : ((False ∨ p2) ∨ ((p3 ∨ ((p4 ∨ (False ∨ (True → (p4 → p4)))) ∧ (p4 ∧ p1))) ∨ (((True ∨ True) → (p4 ∨ ((False ∨ p3) → True))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172225646145180915644942775692 : (((p2 → ((p2 → (False ∨ p1)) ∧ (p3 → (p3 ∨ p4)))) → ((True ∧ p2) ∨ p4)) ∨ (p2 → (p2 ∨ (((p3 ∨ (p5 ∧ p1)) → True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344410930328959439671212987412 : (p2 → (p5 ∨ ((False ∨ (((p3 → (((((False → p5) ∧ False) ∧ p4) ∨ p1) → (p3 ∨ p2))) ∨ ((p5 → (p1 → False)) ∧ p4)) → p1)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46038892341051242763561851266 : ((((p1 ∨ (p4 → (((p3 ∨ (p2 ∧ True)) → ((p2 → p4) ∨ p1)) ∧ (((p2 ∧ p5) ∧ (p5 ∧ p5)) ∨ p3)))) ∧ True) ∧ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746189222416980066264149368395 : ((((p1 ∨ p3) → ((((p2 ∨ (True → p5)) → ((False → ((p3 ∧ p2) ∧ p1)) ∧ ((False ∨ p1) ∧ p5))) ∧ p1) ∨ ((p3 ∧ p5) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50655836455309185805143341563 : (((((True → ((p3 → True) ∨ True)) → (p1 ∨ True)) ∧ (((True ∧ (p4 ∨ p2)) → (p3 ∨ p4)) ∧ p3)) → (((p4 → p5) ∧ False) ∨ p3)) ∨ p2) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136832365961615647546114902641 : (((p1 ∧ True) ∨ (p2 ∧ ((p5 → ((p3 ∧ p4) ∨ ((p1 ∨ (True → p4)) ∨ (p4 ∨ ((p3 ∧ p2) → p1))))) ∧ p1))) ∨ ((p4 ∧ False) → False)) := by
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
theorem thm_5_vars_62657650857066273186585780618 : ((p4 ∧ ((((p4 ∨ p4) ∨ (((False ∧ ((False → p1) ∨ (p4 ∨ p1))) → (p3 ∧ ((p3 → p1) ∨ p2))) → p3)) ∨ (True → p4)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667413635121787483430413711897 : (((((p2 ∨ True) → (False ∧ (((p2 ∧ (p2 ∨ ((((False → p2) → p4) ∧ True) → True))) ∨ (p2 ∧ p2)) ∧ p2))) ∧ (p5 → (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71083082828129743450140396696 : ((((((False ∧ p1) → (p4 → p4)) → p4) → ((((p3 ∧ p4) ∨ p5) → (((((True → p3) ∧ p3) → False) ∨ False) ∧ False)) ∧ False)) ∧ p4) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∧ p1) → (p4 → p4)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338090417791605121245103978717 : (p1 → (((((p5 ∧ (p3 → p3)) → p3) → p2) ∨ True) ∧ ((p5 ∨ (p1 ∨ (p2 ∧ p4))) ∧ (p5 ∨ (((False ∨ False) ∨ (False ∨ p1)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338465540839690962465977310649 : (p1 → (((False → p1) → True) ∧ ((p2 → p4) → ((((((p4 ∧ p2) ∧ p1) ∧ p5) ∨ (True → p5)) ∧ ((False ∧ (p2 ∧ True)) ∧ False)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313246560070998223083225339122 : (p3 ∨ (((True ∧ p3) → (((((((p3 ∨ False) ∨ p5) ∧ True) → (False ∧ p4)) ∨ (p4 ∨ False)) ∨ (True ∧ (True ∧ (p4 ∨ False)))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621147122656631894649505239802 : (((((p5 → p2) → ((True → p5) ∨ ((p2 ∧ (p3 ∨ p5)) → (((p5 ∧ (p5 → (p5 ∨ p3))) ∧ (p5 → p2)) → (False ∧ False))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258788962904597624674324052738 : ((True → False) → (((p4 ∧ p2) ∧ (False → (p4 ∧ (False ∧ p4)))) ∨ (p3 ∨ ((((p4 → (p1 → (False → (p4 → True)))) ∨ False) → p2) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249561299728441643409532225659 : ((p5 ∨ p2) ∨ ((p1 ∧ (False ∧ (p1 ∨ p5))) ∨ ((p5 → p1) ∨ (((False ∧ p2) ∧ False) → (((p2 ∨ p2) → p2) → ((p5 ∧ p2) ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_557072920289840077830191469551 : (((p3 ∨ ((p3 ∧ (((p1 ∧ True) ∨ (p2 → (True → p3))) ∨ True)) → (((False ∨ p3) ∧ (p4 ∧ (False ∨ p5))) ∨ ((p5 → False) ∨ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117067910312191690139142929601 : (((True → False) → ((((True ∨ (p4 → (p2 ∨ p1))) ∧ (((p3 → True) ∨ True) → (((p5 ∧ p4) ∧ p2) ∨ p1))) ∨ p3) ∨ p3)) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133873652053746086031468538585 : (((p4 ∧ ((p4 ∧ ((p2 ∧ ((p5 ∨ (p5 ∧ (True → ((True → (True ∧ p2)) ∨ p3)))) ∧ p4)) ∧ p3)) ∧ p4)) ∧ p2) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150069349818286909657324586916 : ((True → ((((False ∨ p5) ∧ p1) ∨ (p4 ∨ (p5 ∨ p1))) → ((p3 ∨ (p3 ∨ False)) ∧ (p5 ∨ (p5 ∧ p1))))) ∨ ((True ∧ p4) → (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689499325067917779718082782233 : (((((p5 ∨ (True → ((p5 ∧ (True → False)) → (p3 → p5)))) → ((p2 ∨ p1) → p4)) ∨ (False → (((False ∨ (p1 ∨ p4)) → p2) → p3))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_354048960700066017737442210222 : (p4 → (p4 → ((p1 ∧ (p1 ∧ False)) ∨ ((p2 ∧ (True → (((p3 ∨ (False ∧ (p3 → ((p5 → (p2 → p4)) ∧ p1)))) ∨ p3) ∨ p1))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304673433409238376896546342524 : (p1 ∨ ((((p1 → ((((p2 ∨ ((True ∨ p2) → True)) ∨ ((p4 ∨ ((False ∧ True) → p1)) ∧ p1)) → p2) → p2)) ∧ p4) ∧ p2) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171702168203232018802146020304 : (((p2 → ((p1 ∨ p4) ∧ (p4 ∨ ((((False ∧ p5) ∨ False) ∨ p1) → p4)))) ∨ p3) ∨ ((((p2 ∧ p2) ∨ True) ∨ (p1 ∧ True)) → (True ∨ False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54828228292997266881079076703 : (((p1 → ((p5 ∨ (p5 ∧ (p3 ∨ p2))) ∨ p1)) → ((True ∧ True) → ((p1 ∧ p4) → (((p2 ∨ (p1 ∨ (p3 → p2))) → p5) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h2.left
  let h7 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58171120319285491289512050688 : (((p3 ∧ p1) ∧ (((((p1 ∧ (p5 ∧ True)) ∧ False) ∨ p5) → (False → ((False ∨ (p5 → (p1 ∨ p4))) ∧ p3))) → ((p1 ∨ p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212562361448278998637700577288 : ((p5 ∨ ((p2 ∧ False) → p4)) ∧ ((((True ∧ (p5 ∨ (True → (((p2 ∧ p4) ∨ (p3 ∧ (False ∧ p1))) ∧ (p1 ∧ p4))))) ∧ False) ∧ p5) ∨ True)) := by
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
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669048382008108446637511336265 : (((((((p1 ∨ ((((True ∨ (p1 ∨ False)) → False) ∨ ((p3 ∧ (p4 ∧ p1)) ∧ False)) ∧ p1)) ∨ p5) → True) → p4) ∨ (False → (p5 → False))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_609812926825425667593627647409 : (((((True → (p4 ∧ (((False ∧ (p4 ∨ p4)) ∨ (((p2 → False) → (p2 → p3)) ∨ ((p4 ∨ p4) → (p2 → p1)))) → p4))) ∨ p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_649290411507450403590557804888 : (((((p5 ∧ ((p2 ∨ ((True ∨ False) → (p3 ∧ (p2 ∧ (False → True))))) → ((p3 → ((p1 → p2) ∧ p2)) → p5))) → p4) ∧ (False → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245596948929705212177251133475 : ((p3 ∧ False) ∨ ((((p3 ∧ True) ∧ ((p5 ∧ (p4 ∨ True)) → ((True ∧ (p1 ∧ p4)) ∨ (False ∨ ((p3 ∨ False) → p3))))) ∨ p2) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321668322228693970425758304538 : (p4 ∨ (p4 → ((((p5 ∧ p3) ∧ (((((((p4 ∧ p3) → (p3 → p3)) ∨ p4) → (p1 ∨ p2)) → p2) ∨ False) ∧ p2)) ∧ p1) ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348090760766902901133615972642 : (p3 → ((p1 → p2) ∨ ((p3 ∧ ((p4 ∧ (False ∧ p2)) → ((p2 ∧ p5) ∨ ((False → p5) ∨ (p4 ∧ False))))) → ((p3 → p4) → (p2 ∨ p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206866659229867654116019336969 : (((((p1 ∨ p4) → p1) ∧ p4) ∧ p3) → ((p2 → p1) → (((p3 ∧ ((((True → (p3 ∧ (p5 → p4))) → p4) → False) ∧ p2)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246346019384536401605456329078 : ((p4 ∧ p5) ∨ ((True → (p4 ∨ False)) → ((((p1 → p3) ∨ p1) ∨ ((p5 → (p2 ∧ True)) → ((True ∨ ((p4 → p2) ∨ p2)) ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58311317491570603155500679407 : (((True ∨ p5) ∧ ((p3 ∨ (p1 ∨ (((p3 → (p4 ∧ True)) ∧ ((((p4 ∧ False) ∧ p3) ∧ (p5 ∨ False)) ∨ p3)) ∨ p3))) ∨ (p1 ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215809447905338855639103212993 : ((p1 ∨ (p4 → (False ∨ p3))) ∨ (p3 ∨ (p2 → ((p3 → (p3 → p4)) ∨ (((p2 ∨ (p2 ∧ False)) → ((False ∨ (p4 ∧ False)) ∧ True)) → False))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ (p2 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730200623086486083342707149680 : (((((False → p1) → p4) → (((p2 ∧ True) ∧ (p1 ∨ (((p1 ∧ (p5 ∧ True)) ∧ True) ∧ p3))) → (((p3 ∧ False) ∨ (p5 ∨ p1)) ∨ True))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210436244771097654113932635631 : (((p5 ∨ (p4 ∧ False)) ∨ True) ∧ (((False ∧ p4) ∨ ((p2 ∨ (True → (p5 ∨ (((False ∨ p2) ∨ ((True ∧ p2) ∧ p5)) ∧ p4)))) → True)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153606271148321711586461918729 : ((False → (True → ((((p4 ∨ p2) ∨ p4) → ((p2 ∨ p4) ∨ ((p2 → True) → (False ∧ (p1 ∨ p3))))) ∧ p4))) → (((p3 → p1) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151032019496952953228710616567 : (((((p4 ∧ ((p1 ∨ (((p1 ∨ p2) ∧ (p3 ∧ p3)) → p5)) ∧ ((False ∨ p2) → False))) ∨ p2) ∧ p4) → p2) → ((True → p3) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52486725331732623341747547112 : (((p1 → (p5 ∧ (((p1 ∨ (p2 ∧ p3)) ∧ (False → p3)) ∨ (p3 → p4)))) ∧ ((p3 ∧ (p3 ∧ p3)) ∨ (p4 ∧ (p2 ∨ (False ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343179733569824741397613556961 : (p2 → ((p5 ∨ (p5 → p4)) ∨ ((False ∨ ((p1 → ((True ∨ True) ∧ (True ∧ p4))) ∧ (p2 ∨ True))) → (((p4 ∧ (p1 ∧ p2)) ∨ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53232226596499689771951217574 : ((((p1 → (True ∨ (p5 ∨ p3))) → (p1 → (p3 ∨ (p5 ∧ p2)))) ∨ ((True ∨ ((True ∧ p2) ∧ False)) ∨ ((p1 → (p3 ∧ True)) ∧ p3))) ∨ p1) := by
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
theorem thm_5_vars_198950132051188464311661241804 : ((p4 → (False ∧ (False → (False ∨ (p1 ∧ p2))))) ∨ (p4 → (p5 ∨ (((((p1 ∧ True) → False) ∧ (p5 ∧ p2)) ∨ p1) ∨ ((p5 ∧ False) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_801429220286347648050643335748 : (((p2 → ((((p4 ∨ (p1 → True)) → p3) ∧ (p4 → (p5 ∨ p2))) ∨ (((True → p1) ∨ (p4 ∧ (p1 ∧ (p2 → p5)))) ∨ (p3 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232150917706072273864290453289 : (((True → p1) → p5) → ((p4 → (((True ∧ (False → (p1 → ((p1 ∨ p3) ∧ p2)))) → (p3 ∨ p2)) ∨ p4)) ∨ (p4 → ((p5 ∨ p4) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



