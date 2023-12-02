variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102724830027352020845774212245 : (((((p5 ∨ False) ∨ (((p4 ∨ True) → ((True ∨ p1) ∧ ((p4 → p3) ∧ p3))) → (p1 ∧ ((p1 → p5) → p3)))) ∨ True) ∨ False) ∧ (False → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64436033764396808612652092548 : ((p1 ∨ (((p1 → (((False ∨ ((True → ((p1 → p3) ∨ (p2 ∧ (p4 → p4)))) ∨ False)) ∧ (p5 ∨ p2)) ∧ p5)) ∧ p3) ∨ (False → False))) ∨ p1) := by
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
theorem thm_5_vars_138342732269904811298440350520 : ((p4 → ((p3 ∨ (((p4 → p4) ∧ p5) ∨ ((False ∧ p4) ∧ (p4 ∧ (((p4 ∧ p4) ∧ (p5 ∨ True)) ∨ False))))) ∧ p4)) ∨ (p1 → (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136461133515341311402300369792 : (((p3 → ((False ∨ p1) ∧ p5)) → (((p4 ∨ ((p1 → (p1 ∧ p4)) → (p4 ∨ p1))) ∨ p1) ∨ (False → (p3 → p1)))) ∨ ((p5 ∧ p1) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114006819044459356572932479962 : (((((((p5 → p3) → p4) → ((p4 ∨ p5) ∧ p2)) ∨ ((p5 → (False ∧ (p5 ∧ False))) ∨ p2)) ∧ p5) ∨ ((True ∧ p1) → False)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198433747397454012197639229428 : ((p4 ∧ (p4 ∨ (True ∨ ((p4 ∨ True) ∧ p1)))) ∨ ((p2 ∨ ((True ∧ ((p1 ∧ p5) ∨ (True ∨ (False ∧ p1)))) ∨ ((False → p3) → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68364711490693098444301778335 : ((p3 → ((((False → True) ∨ p5) → (p1 ∧ p2)) ∧ (((p2 ∧ (True → (p2 ∨ (p4 ∨ p2)))) ∨ p3) → ((True ∧ (p1 → p4)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116869803472452580956733175702 : (((p2 → False) ∨ ((((((p5 ∧ False) → (True ∧ True)) → p3) ∧ ((p4 → p4) ∧ ((p4 ∧ True) → p3))) ∧ p4) ∧ (p1 ∨ True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350137987840627899738406558766 : (p4 → (((p1 → ((p3 → p4) ∧ (p5 ∨ ((p1 → ((False ∨ p2) → p5)) ∧ False)))) → (((((True ∨ p4) → p3) ∧ p2) ∨ p2) → False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231627947469932912610181793208 : (((False ∧ True) → p5) → ((p2 ∧ (p2 ∧ (((p3 → ((p5 ∧ (p2 → p1)) ∨ (p2 ∧ p1))) ∧ p1) → (p1 → True)))) → ((p5 ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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
theorem thm_5_vars_746935094744596061374601338451 : ((((p4 ∨ p1) → (((p5 ∨ False) ∨ (((p2 ∨ (True ∧ p3)) ∧ p5) ∨ ((p3 ∨ (p1 → ((False ∧ p1) → p5))) ∧ p1))) ∨ (p2 → p2))) ∨ p4) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233022542490345549674506984932 : ((p4 ∧ (p2 ∧ p5)) → (((True → False) ∨ ((p1 → (p3 ∧ False)) → (p3 → (p1 ∧ p3)))) ∨ ((True ∨ ((False ∧ (p1 ∧ p3)) ∧ False)) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599422513588005533200932536092 : (((((p5 ∧ p4) ∨ ((((p4 ∧ p3) → p1) → ((True → (p4 ∨ p5)) ∨ (True ∧ ((((p1 → True) → True) ∨ p3) ∨ p2)))) → p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156594009545314619043828152565 : (((((((((p1 ∨ p3) ∧ False) → (p5 → ((p4 ∧ p2) ∨ p2))) → False) ∧ True) ∨ p1) ∧ p1) ∧ True) ∨ (((p3 ∨ p3) ∧ p5) → (p2 → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118616436703146077460484437982 : ((p4 ∨ (((p2 ∧ (((p4 ∧ (True ∨ p2)) ∧ False) ∨ p4)) ∨ (p2 ∧ False)) ∨ (p5 → (((False ∧ (p4 ∨ p3)) → True) → p1)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192879517900097849300832345803 : (((True ∧ (p5 → ((p2 ∨ p4) → False))) ∧ (True ∧ True)) → (((((p2 ∧ (p3 ∨ p3)) → p1) → (p2 ∨ p3)) ∨ (False → p1)) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731549505219405961594541631715 : ((((False → (p4 ∨ p5)) → (((p1 → p1) → p1) → (p3 → (((p2 ∨ (((False ∨ p1) ∧ (p4 → p2)) ∨ p1)) ∨ p4) → (p2 → p1))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h19 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h19
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642888095064585178353179224058 : ((((p2 ∧ ((p4 ∧ (p1 ∨ (p4 ∧ ((((((p5 → (p5 ∨ (p3 ∧ p5))) ∧ p1) → (True ∧ p2)) ∨ p3) → p1) → p4)))) → p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803413232735336274045847250699 : (((p3 → ((True → (((p1 ∧ (p1 → p1)) ∧ (((p4 → p1) ∧ True) → ((p1 ∨ ((p4 ∧ (p2 ∨ p3)) → p2)) ∨ p5))) → p4)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111893269066990034311613507810 : (((((p2 ∨ (True ∨ (((p4 → (p1 → p5)) ∨ p3) ∨ (p4 ∧ p1)))) → False) ∨ (((p1 ∧ (False ∧ p5)) ∧ p4) → p1)) ∨ False) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619918530853888361208542575447 : (((((True → p4) ∧ ((p2 ∧ (((p3 ∨ True) ∧ (p1 → (p1 ∨ p3))) ∧ (((True → p1) ∨ p1) → (p1 ∨ (p2 → True))))) → p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157463023617979557071895433699 : ((((((p5 ∨ (p5 ∨ (p3 ∧ p5))) ∧ p4) ∨ (p3 ∧ (p4 → (p5 ∨ True)))) ∨ p3) ∨ (False ∨ True)) ∨ (p2 ∨ ((p3 → (p5 → False)) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177703663569595080496280977429 : (((((p1 ∨ (p5 → (p1 ∧ p4))) ∨ (p3 ∨ True)) → (p5 ∨ p4)) ∧ False) ∨ (False → (p5 ∧ ((p3 → p3) ∧ (((p2 ∧ p4) → False) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305953794691901699517036827388 : (p1 ∨ (((True ∨ p3) ∧ (False ∨ True)) ∧ ((((p4 ∨ (p5 ∨ p2)) ∨ (False → False)) ∨ p4) ∨ (p3 ∨ (p3 ∨ (p4 → (p2 ∨ (p5 ∨ p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60160975803768395629676692117 : (((p4 ∨ p5) → ((p3 ∨ (((p5 ∨ ((((p4 → ((True ∧ False) → p3)) ∧ p5) ∧ p3) ∨ True)) → (True ∨ (p4 → p2))) ∨ p4)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184569087545426581343200063356 : ((((True ∨ True) ∧ ((p3 ∨ p2) → (False → True))) → (True ∧ p2)) ∨ (((True ∨ (p3 ∧ (((p4 → p5) ∨ (True ∨ True)) ∧ True))) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165196292189180959387834521442 : (((((p3 ∨ (False ∨ ((True → (p5 → p1)) ∧ (False ∧ p4)))) ∧ p5) ∨ p3) ∨ (p1 → False)) ∨ (((p5 ∧ p2) ∨ (True ∨ (p4 ∧ p5))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60438933219546561451160511591 : (((p4 → p5) → ((p3 ∧ True) → (p5 ∧ (True ∧ (p1 ∧ (((((p2 ∧ True) ∨ True) ∧ (False → p2)) ∧ ((p2 ∧ p2) ∧ p3)) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117812015986731133898560171428 : ((p4 ∧ ((p2 → p2) ∧ ((((p3 → p4) → (p2 → p1)) → False) ∨ (p4 ∨ (((p5 ∧ p4) ∧ ((p2 ∧ p4) → p5)) ∧ p5))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798121293644298604238651507877 : (((p1 → ((False → (p3 ∨ ((((p3 → p2) → (p5 ∧ ((True ∨ False) → (False → True)))) ∧ (True ∨ p2)) ∧ p3))) → (p1 ∧ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128483032872253390416791867362 : ((p5 → ((((((((p5 → (p2 ∨ p3)) → p2) ∧ p2) → True) ∧ p3) ∨ p3) ∨ (p1 ∨ False)) → (False ∨ ((True ∨ p2) → p4)))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386078582742771709826263004224 : ((((((p2 → (((((p3 ∨ p4) ∧ p1) ∨ p5) ∧ (p5 → True)) ∨ ((p2 ∧ (p2 ∧ p5)) ∧ False))) ∧ (p1 ∨ False)) ∨ (p4 → True)) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137817351302294029137981258084 : ((p3 ∨ ((((False ∨ (True → ((True → p2) ∨ (p2 ∨ False)))) → p1) ∧ ((p1 → (p3 → (p1 ∨ p1))) → True)) ∨ p4)) ∨ ((p2 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117237023755448837365072783465 : ((True ∧ (p4 ∧ ((p4 → (False ∨ ((False ∧ (p5 ∨ p5)) ∨ p4))) ∨ ((p2 ∧ p5) → (((p5 → False) ∧ (p3 ∧ p5)) → False))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308551269577183219892423650672 : (p2 ∨ (((True ∨ ((p3 ∧ p3) → ((p2 → p4) ∧ p2))) ∧ (((p4 → p5) → p2) ∧ ((p3 ∨ ((p3 ∧ (p5 → p3)) ∨ p2)) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150429759327512657620049514281 : ((((p1 ∨ ((((((p2 ∨ (p4 ∧ p3)) ∨ p3) ∨ (p2 → (p2 → p4))) → p3) ∧ False) ∨ p1)) ∨ p2) ∧ p4) → ((p4 → p3) ∨ (p2 ∨ True))) := by
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
        -- False on the left can always be used.
        apply False.elim h9
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114912007020502762393398121471 : ((((((((p1 ∨ p1) ∧ True) ∧ p2) → (True ∧ (p5 → p2))) → p2) ∨ p2) → ((p1 ∧ p2) ∧ (((p1 ∧ p4) ∧ True) ∧ p3))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67809152042329046059535310892 : ((p2 → ((((p5 ∨ False) ∨ p3) ∧ (((p5 ∨ (((p1 ∧ True) → (False ∨ p1)) ∨ True)) ∧ (False ∨ ((True → p5) ∨ p3))) → p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131727497216592128883121192853 : (((p5 → (p4 ∧ p1)) → ((((((p4 ∨ False) → ((p4 → (p1 ∧ True)) ∧ p3)) → p4) ∧ p4) ∨ p4) → (p4 ∨ p3))) ∧ ((False ∨ True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199146115054717659736983274101 : ((((p4 ∧ p1) ∨ (p3 ∧ (p4 ∨ p3))) ∧ p3) → (((True ∧ ((p5 ∨ p2) ∨ ((p2 ∧ (p1 ∨ p3)) ∨ False))) ∧ False) ∨ ((False ∨ p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44541129122336107123111820354 : (((((p5 ∧ p4) → (((p4 ∨ (p5 ∧ True)) → False) ∨ p2)) → (p4 ∨ ((p2 → ((True ∧ (p1 ∧ (p5 ∨ p3))) ∧ p4)) ∨ p4))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39868935109962000227184212171 : (((p2 → (((p4 → (p2 ∧ (((((p3 ∨ False) ∨ (True → False)) → (True ∧ (p4 ∨ p4))) → (p1 → p3)) → p3))) → p3) ∨ p4)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249032549222154593233207576514 : ((p4 ∨ False) ∨ (p3 ∨ (p5 ∨ (p3 → ((p1 ∨ (True ∨ (((p5 ∨ (p2 ∧ (p4 ∨ (p4 ∨ (False → p3))))) ∨ (False ∧ p4)) ∨ False))) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201185080723791043367441286215 : ((p1 → (((p4 ∧ p5) → p4) → (True ∧ p3))) → (((((p1 ∨ (p2 ∧ (p5 ∧ p5))) ∨ p4) ∨ (((True ∨ p3) → False) ∧ True)) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258229973438878982578442654997 : ((p4 ∨ p5) → ((p2 → ((((p2 ∨ True) → p1) ∧ (((p4 ∧ ((p3 ∨ (p4 ∨ p4)) ∨ True)) → True) → (p5 → p3))) ∨ p5)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231401175462991928336927616191 : (((p1 → p1) ∨ p3) → (((p5 ∨ ((((((True ∨ (False ∧ p1)) ∨ p5) ∧ True) ∧ (False ∨ p5)) ∨ ((p3 ∧ p4) → p1)) → False)) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_758775091985828636307384112926 : (((p2 ∧ ((p5 ∨ (p1 ∧ ((p1 → ((p5 ∨ p5) → ((p4 → p2) ∧ (((p3 → ((p4 ∨ p1) → False)) ∨ p5) → p5)))) → p4))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157184414081401541311373525253 : ((((p2 ∧ (p2 ∨ (((p1 ∧ ((p3 → p2) ∧ ((False ∧ False) → True))) → True) → p2))) → p3) → p2) ∨ (True ∨ ((p4 ∨ (False ∨ p3)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766622924455451737983674645966 : (((p4 ∧ (p5 ∧ (p5 ∨ ((False ∨ (((p2 ∧ p3) ∧ ((True ∨ True) ∨ p1)) ∧ False)) ∨ ((p3 → (p4 ∨ ((p2 ∨ p3) ∧ p3))) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350054282547953139209735407306 : (p4 → (((((((p5 → (p1 → True)) ∧ (p3 ∨ p3)) ∧ p3) → ((p3 ∧ True) → (p1 ∨ ((p1 ∧ p5) ∨ p3)))) ∨ p5) ∧ (p4 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657428141293784125800064545750 : (((((True ∧ p4) ∨ (((p3 → p2) ∨ (p4 ∧ ((((False ∧ True) ∨ p3) ∨ (p4 ∧ (True → (p2 ∨ True)))) ∧ p2))) ∨ p5)) ∨ (True ∨ p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_773438769715116929704860779220 : (((False ∨ (((((p5 ∧ (((True → (True ∧ p2)) → (p4 ∨ (True ∨ (p2 ∨ (False ∨ p3))))) ∨ p3)) ∨ p5) ∨ (p5 ∧ p5)) ∨ True) ∨ p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_224138565847354442345167378447 : ((p5 ∨ (p5 → True)) ∧ ((p1 ∧ ((p2 → p5) ∧ ((p3 ∨ p1) ∧ ((((p2 ∨ p1) → p1) ∨ ((p1 ∨ p5) ∨ p2)) ∧ (p3 ∨ p3))))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165034730323415685396003502099 : ((((True → (p5 → p5)) → ((False → ((p3 ∨ (p5 ∨ p4)) ∨ (p3 → p2))) ∧ False)) → False) ∨ (p2 ∨ (p2 ∧ (True ∨ ((p2 → False) ∧ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (p5 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173126319387381878398778184451 : ((p2 ∨ (False ∧ (p3 ∨ (p1 → ((((p2 ∧ True) → p5) ∨ (p1 ∧ p3)) → p4))))) ∨ ((p3 → ((p4 → p2) → p3)) ∨ ((p5 ∨ p4) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138709475730483648696519304205 : ((((((p3 → p1) ∧ (p3 → (p3 ∧ True))) ∧ True) → ((((True → p3) → (True → p2)) ∧ (p3 ∧ p1)) ∧ True)) ∧ p1) → (p3 ∧ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 → p1) ∧ (p3 → (p3 ∧ True))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140795917054201219705267960566 : ((((p3 → p5) ∧ (p4 ∧ ((p4 → (True ∧ p3)) ∨ (p3 → p1)))) ∧ (((p2 ∨ p3) ∨ ((False → p3) → p3)) → False)) → ((p5 ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_58023101286760326634402137898 : (((True ∧ p3) ∧ ((p4 ∧ ((((p2 ∧ p1) ∨ p2) ∧ (True ∨ p2)) ∧ ((True ∨ ((p4 ∨ True) → p5)) ∧ ((p4 ∧ p1) → p2)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215170200523366859773618061806 : ((True ∧ ((p1 → False) ∨ p2)) ∨ (False ∨ ((False → (((True ∨ p5) ∨ (((False → p5) ∨ False) ∨ p1)) → (p1 → p2))) → ((True → False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56109851415199849904359578247 : ((((p5 → p4) ∧ (False → p2)) ∨ (p2 → (((p3 ∨ p3) ∧ ((False ∨ p1) ∧ ((((True ∨ False) ∨ True) ∧ p2) → False))) ∨ (p5 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181638221180436508246910863493 : ((p3 → ((p3 → ((((True ∨ p4) → p1) ∧ (p3 ∧ True)) → p5)) ∨ p1)) → ((p1 ∨ (p2 ∨ (True ∨ (False → (True → True))))) ∨ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_317946997516738486354820118379 : (p4 ∨ ((p3 ∨ (p2 ∨ (((p4 → True) → (p3 ∨ ((False ∨ ((True ∨ p4) ∧ (p1 → ((True ∨ (p1 ∧ p1)) ∧ p5)))) → p3))) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158714576351091983481109380460 : ((p3 ∧ (((p1 ∧ (p4 ∧ (p1 ∨ (p3 ∨ p1)))) ∨ ((False → (p2 → p4)) → p2)) ∧ (p3 ∨ p4))) ∨ ((p4 ∧ ((p5 → False) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305863925977413883887646262998 : (p1 ∨ (((((p4 ∨ True) → False) ∧ p1) ∨ p1) ∨ (p4 → ((p3 ∨ (p2 → p3)) ∨ ((((p5 ∨ p3) ∧ (p5 → True)) ∧ (False ∨ p3)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_125381142207177952796187862883 : (((True ∧ p2) ∧ (((((p5 → ((((p4 ∨ p2) → p3) ∧ p5) → p3)) ∨ p2) → ((p1 → (p4 ∨ p4)) ∧ False)) → True) ∨ p5)) → (p3 → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57763212499781265211691799542 : ((((p4 → p2) → p2) → ((((((((False ∨ p5) ∨ (p5 ∨ p3)) ∧ True) ∨ p1) ∧ (((p2 ∨ True) ∨ False) → p1)) ∨ p3) ∨ p3) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351902960188189758345814016305 : (p4 → (((((p2 ∧ p4) ∨ p5) → (p5 ∧ (p5 ∨ p2))) → p1) ∨ ((((p2 ∧ (True ∨ (p2 → p1))) → (True ∧ False)) ∨ p2) ∨ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186846727200839838231091709997 : (((p3 ∧ ((True → p4) ∨ p4)) ∨ (p3 → ((True → False) ∨ p1))) → ((False ∨ ((False ∨ (p4 → p2)) ∨ (p4 ∨ ((p1 → p4) → p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763573253498805438129897178499 : (((p3 ∧ (p4 ∧ (((((p4 → p2) ∧ (p1 ∧ ((True → p2) ∨ p1))) ∨ (False ∨ (((p5 ∧ p4) ∧ (False ∧ p4)) → p5))) → False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229925681669084359977538350246 : ((p5 → (p5 → False)) ∨ (((p5 ∨ (((p3 ∨ (p1 → ((p5 ∨ False) ∨ True))) ∧ (p1 → True)) ∨ p4)) ∨ ((p1 ∨ p1) ∧ p4)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785398564094932069629103684403 : (((p4 ∨ (((p1 ∨ (p1 ∧ (p2 ∨ (((p5 → ((p2 ∧ (p5 → p1)) ∧ False)) → False) ∨ (p1 → (p5 ∨ p2)))))) ∨ (p3 ∨ True)) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684291645303791167381318742547 : ((((((p4 ∧ p1) ∨ (False ∧ (p5 ∧ (False → (p1 ∨ (p1 → p5)))))) ∨ ((p2 ∧ p5) ∧ False)) ∨ (p3 ∨ (False ∨ (False → (True → p3))))) ∨ p1) ∧ True) := by
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208466347034916577163709309853 : (((p3 → False) ∨ ((p2 ∧ p5) ∨ p1)) → (((p1 ∧ ((p1 → p1) ∨ False)) ∧ (((p4 → True) ∨ p2) → ((p5 → (True ∧ p4)) ∧ False))) → p2)) := by
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
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 → True) ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h18 : ((p4 → True) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h18
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356046629932195052691037913014 : (p5 → ((p1 ∨ (((((p1 ∧ (p2 → p3)) → False) ∨ (p3 ∧ False)) ∧ p1) ∨ ((p2 → p5) ∨ (p5 ∨ p3)))) ∨ (True ∨ ((p3 → p3) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140294499242606681665095620094 : ((((True ∨ (p1 → p2)) ∧ ((((p5 ∧ False) ∨ True) → ((p1 ∨ True) → p3)) ∧ (p4 ∨ p3))) ∧ ((True → False) ∨ p3)) → ((False ∨ True) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350351204763014200053401495876 : (p4 → ((p4 → (((p1 → (False ∧ (((p3 ∧ True) ∨ True) ∧ (p3 → p2)))) ∨ p4) → (False ∧ ((p2 ∧ (p4 → p1)) ∧ (p4 → False))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207371147186996342511952744551 : ((((p5 → False) → (p2 ∧ False)) ∨ True) → (((p5 ∧ p3) ∨ (p1 ∧ (False ∧ ((p1 → (p5 → (p2 ∧ p3))) ∧ ((p2 ∧ p2) → p4))))) ∨ True)) := by
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
theorem thm_5_vars_644283376401589010026577376768 : ((((False ∨ (((p4 ∨ True) → (((p3 → (((p5 ∧ (((p3 ∨ p3) ∨ p4) ∨ p5)) ∨ p3) ∨ True)) → p3) ∨ p3)) ∨ (False → p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49210520746988646628714580869 : ((((p5 → (True → False)) → (((p3 → (((p4 ∧ p4) → p2) ∨ p3)) ∧ p5) ∧ ((p4 → (p2 ∧ p4)) ∨ p5))) ∨ (p2 ∨ (p3 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56807121052111259560952821257 : ((((p3 ∨ False) → p4) ∧ (((True ∧ ((p3 → (p2 → (p4 → True))) ∧ True)) → (((p4 ∨ p5) → False) ∧ ((p1 ∨ p4) ∨ p5))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43758323807595527378690058351 : ((((p2 ∧ ((((p4 ∨ (p5 ∧ ((False → p4) ∨ ((False → ((True ∨ p2) → False)) ∧ True)))) ∧ (p1 → False)) → False) ∨ p2)) → False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44076611998138571469492905800 : (((((p4 → (((p1 ∨ (p1 ∨ (p2 ∨ p4))) ∨ p5) ∧ False)) → (p5 ∨ (p5 ∧ (p2 → (p2 → p2))))) ∧ (p3 ∨ (True → False))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760400837684561653200308719395 : (((p2 ∧ (True ∧ (((False → (True ∧ (p4 ∧ (False ∨ ((((p3 ∧ (p3 → p1)) ∧ (p1 → True)) → p5) ∧ (True ∨ p2)))))) → p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55172712920902267194076107045 : (((((p4 ∨ (p4 ∨ True)) ∧ p2) → p4) ∨ (p1 ∨ ((p3 → ((((((p1 ∧ p5) ∨ True) → p2) ∨ (p3 ∧ p5)) ∧ p3) ∧ True)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227821661929342206020318275819 : ((p2 ∧ (p2 ∧ True)) ∨ ((((p4 ∨ ((((False → True) ∧ (p2 ∧ (p1 → (p1 ∧ p3)))) ∨ (False ∧ p5)) ∧ p3)) → (p4 → p1)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801384839478370634570428280705 : (((p2 → (((((p4 ∧ p2) → (p3 → p4)) ∨ (p2 ∧ False)) ∧ (p1 ∨ p5)) → ((((p4 ∨ p4) ∧ (p2 ∨ p3)) ∨ (False ∧ True)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61589540618436062417742336059 : ((p1 ∧ ((p5 ∧ (False ∨ p4)) ∧ (((p4 ∧ (((False ∧ p1) ∨ (p4 ∨ p3)) ∧ ((p2 ∨ p5) ∨ (p4 ∨ (p5 → p4))))) → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70833763132422760140472643111 : (((((p4 ∧ (((p3 ∨ p3) → ((p4 ∨ p4) ∨ p1)) → False)) ∧ p4) ∧ (((((p3 → p1) ∧ p4) ∨ p5) ∧ (p4 → p2)) ∧ p2)) ∧ p1) → p3) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h17 : ((p3 ∨ p3) → ((p4 ∨ p4) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h21 := h9 h17
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h23 : ((p3 ∨ p3) → ((p4 ∨ p4) ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h27 := h9 h23
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51623084951954311914780526816 : (((((True → False) → (p3 ∨ (((p4 ∧ (p5 ∧ (p1 ∧ p1))) ∨ p4) ∧ False))) ∧ p4) ∧ (((p1 ∨ (False ∧ p5)) → (True ∧ False)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216928165078069811889873700471 : (((True → (p4 ∧ p4)) ∧ p5) → ((p4 → ((((p5 ∨ p5) ∧ False) ∨ (p3 ∧ ((True ∧ (p4 → p1)) ∨ p4))) → p2)) → ((p2 ∨ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338625099968086956366020903837 : (p1 → ((False → (p1 ∨ False)) → (p4 ∨ (((((p5 ∨ (((p2 ∨ (((p3 ∨ p3) ∧ p4) ∧ p4)) → p5) ∧ True)) ∨ False) ∧ p4) ∨ p1) ∨ p3)))) := by
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
theorem thm_5_vars_773905542020131251854935206962 : (((False ∨ ((True ∨ (((p4 ∨ False) → ((((p1 ∧ p5) ∨ False) ∨ p1) ∨ ((False ∧ (False → p5)) ∨ (True ∧ (p1 ∨ False))))) → p1)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133529479580434927767837702973 : ((((((p3 ∧ ((p5 ∨ p4) → p3)) ∨ (((p4 ∨ p1) ∧ p2) ∧ p4)) → (p1 ∧ (p3 ∧ (p4 → p3)))) ∧ p2) ∧ p5) ∨ ((False → p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350099734070537547054529757529 : (p4 → ((((((p3 → ((p1 → p5) ∧ p1)) ∨ True) ∨ (p3 ∧ ((p4 ∨ ((p4 → False) → False)) ∧ False))) → p1) → (False ∨ (True → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787401062524540834201313496882 : (((p4 ∨ (p4 ∧ (((p1 → (True ∨ False)) ∧ p2) ∨ ((p4 ∨ p2) ∧ (p5 ∧ (((p1 ∨ (p3 → p4)) ∧ p4) ∨ ((p3 ∧ p2) ∧ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149180780973886503516917717850 : (((False → p3) ∧ ((False ∧ (False ∧ p2)) ∨ ((((False → p4) → p2) → p1) ∧ ((True ∧ p3) ∨ (p4 → p2))))) ∨ (p3 → (p1 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_112854859959827327474382447421 : (((((p2 ∨ True) ∧ False) ∨ ((p1 ∨ p4) → (p3 ∧ ((False → True) ∨ (((p4 → (p3 ∨ (p3 ∨ False))) ∧ p1) → True))))) → p3) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65434560313933619477052775314 : ((p3 ∨ ((False ∨ p2) ∧ (((((p5 ∧ p3) ∧ p1) ∧ p5) ∨ ((False ∧ p3) → ((False ∧ (True → (p1 ∧ (p2 ∨ p2)))) ∨ p1))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358001730539687449480144272040 : (p5 → (False ∨ ((False ∧ (False ∧ (p2 ∧ False))) ∨ (True ∨ (p3 → (p2 ∧ (p4 ∨ (p3 → (p5 ∧ (p1 ∨ ((p5 ∧ (p1 ∨ p1)) ∨ p3))))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313126880512785375969263195036 : (p3 ∨ ((((((True ∨ (False ∨ p4)) → True) ∨ True) → ((p2 ∧ (p1 → False)) → ((p3 → True) → p3))) ∨ (p2 → (p2 ∧ (p3 → p2)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



