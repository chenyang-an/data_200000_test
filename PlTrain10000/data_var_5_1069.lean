variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137197435809944512094740902184 : ((False ∧ (p2 ∧ ((((p4 ∧ ((p5 → (p4 → (p5 ∨ (p5 ∨ p1)))) ∨ p3)) → p2) ∧ False) ∧ (p5 → (p1 ∨ p3))))) ∨ ((p2 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185611143553637588574529676810 : ((True → ((p3 ∧ (p1 ∨ ((True → p1) ∧ (p4 ∧ p1)))) ∨ p5)) ∨ ((((((True ∨ p3) → p2) → p4) ∧ p4) ∨ (True ∧ True)) ∨ (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_701698182454369867884443392731 : (((((p4 → p1) → (p1 ∨ (p3 ∨ ((p4 → False) → False)))) ∧ (p5 ∧ (((((True ∨ p2) ∧ p1) ∨ (p4 → (True → p3))) ∧ True) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797097659462421309074786620035 : (((p1 → ((((p5 ∧ (True → p5)) → p4) → ((((p1 ∨ (p5 ∧ p5)) → p2) ∨ ((p5 ∨ (True → (p4 ∨ False))) → False)) ∧ p5)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117619447395159257442161767332 : ((p3 ∧ ((((p4 ∨ ((p4 → p4) ∧ ((((p2 → (p4 → (False ∧ p2))) ∨ False) ∧ True) ∧ p4))) → p1) → (p2 ∨ p1)) ∧ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257124862301916610079498325544 : ((p2 ∨ p1) → (((((p2 → (p3 ∧ (p1 ∧ (p2 → (p2 ∨ (True → (p3 ∨ False))))))) → p4) ∧ p2) ∨ (p4 → (p5 → (p5 → p4)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2787183472304764636327567760 : (((True → p4) ∨ (p3 ∨ p5)) ∨ (((p2 ∧ (((True ∧ p3) ∧ (p1 ∨ p4)) → ((p1 ∧ (p5 ∧ p2)) → False))) ∧ p1) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156416923423518729522977147580 : ((p1 → (((p2 → (False ∧ ((p4 → p5) → (p4 ∧ p3)))) ∨ ((True → p1) → False)) ∨ (p3 → p1))) ∧ (p5 → (((True ∧ p5) → True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179301104641303711625704946644 : ((False ∨ ((((p5 ∧ p3) ∧ ((p1 → p2) → False)) ∧ p3) ∧ (p5 ∧ p2))) ∨ (((p3 ∧ p5) ∨ False) ∨ (False → (((p3 ∨ p1) → False) → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90296827217106597527181173427 : (((False → (p1 ∧ p4)) → ((False → (p3 → ((p4 ∨ False) ∧ (True ∧ (((True → p1) ∧ ((False ∨ p4) → (p3 → p1))) → p1))))) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p1 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732673804129199491266645549745 : ((((p1 ∧ p3) ∧ (((((((((True ∨ ((p4 → (True → p3)) ∧ p5)) ∧ True) ∧ True) → p2) → False) ∧ p5) ∨ (p4 ∧ False)) ∨ True) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134926566078381875123253595192 : (((((((((p5 → False) → False) → True) ∧ p4) ∨ (((p2 → p5) ∨ (p3 ∧ p4)) → False)) → True) → p4) ∧ (p5 ∧ True)) ∨ ((False ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352480274448854931813650210472 : (p4 → ((p5 ∧ (p3 ∨ p5)) → (False ∨ (p5 ∧ (((p1 ∧ p5) ∨ (p5 ∧ ((False ∨ ((p1 → p3) → True)) ∨ ((p4 ∨ False) ∨ p4)))) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158410339627130545136439933029 : (((p1 ∧ False) ∨ ((p4 ∨ p3) ∨ ((((False → True) → ((False ∧ p3) ∧ True)) → (p1 → False)) ∨ False))) ∨ (p2 → (p2 ∨ (p4 ∨ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644784614051090673957638586913 : ((((p2 ∨ (((p5 ∧ ((p3 → p3) → (True → p1))) ∨ ((p1 ∧ (p5 ∨ p5)) → ((False ∧ (False ∧ (p2 ∨ p1))) → False))) ∨ p3)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118140639890400755784610135374 : ((False ∨ ((p3 → (False → (False ∨ (((p1 ∨ (p3 → (p4 ∨ True))) ∧ False) → p3)))) ∧ (p1 ∧ (p3 ∧ (False ∨ (p2 ∨ p1)))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729740142668829863575810783887 : (((((p3 → p2) ∨ p2) → ((p1 ∧ (((((False ∧ p1) ∨ p5) ∧ False) ∧ False) → ((p3 → (p5 ∧ ((p3 ∨ p3) → p3))) → False))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46684092951182565429030846576 : (((p2 ∨ (((((False → p3) → p4) ∧ True) ∧ (True ∨ p4)) ∧ (p2 ∧ ((True → ((False ∨ (False → p3)) → p1)) ∨ p1)))) ∧ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198369775496491295176557779702 : ((p3 ∧ (((p5 ∨ (p5 ∧ p4)) ∨ p4) ∨ p3)) ∨ ((p3 → p3) ∨ (p1 → ((p4 → ((p2 ∧ False) ∨ p3)) ∧ ((p1 ∧ p5) → (False ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44302660783209649959344373622 : ((((True → ((((False ∧ (True ∨ (False → p3))) → p5) ∨ False) → (True ∨ (p3 ∧ p4)))) ∧ (p2 ∧ ((p1 → p3) → (True ∨ p2)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307496785697897948754378023121 : (p1 ∨ (True → ((p2 ∨ ((p5 ∨ ((True → True) → (p2 ∧ ((((p3 → p5) ∨ p2) ∨ p5) → (False ∨ p2))))) ∨ (p1 ∨ True))) ∨ (p5 → True)))) := by
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
theorem thm_5_vars_61278501491870009323097738932 : ((False ∧ (p3 ∨ (p5 ∧ ((((((False ∨ (((p4 ∨ p3) ∧ p1) ∨ False)) ∧ (True → p1)) ∨ True) ∨ p5) → p5) → ((False → False) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702097928376229651982445809429 : ((((p2 → (p5 ∧ (((p1 ∨ p5) → p1) ∧ (p1 ∧ False)))) ∧ (p2 ∧ ((((False ∨ ((False → False) ∧ p3)) ∨ p5) ∧ (p4 → p5)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134325424832791626487230419246 : (((p2 ∧ ((((True ∧ (((((p4 → p4) ∨ p5) ∧ (p3 → True)) ∧ p2) → p1)) ∨ p4) ∨ p3) ∧ (p2 ∧ p1))) ∨ True) ∨ (True → (p2 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198533454192225365142501308542 : ((False ∨ ((p3 ∨ p5) ∧ (p1 ∧ (p2 ∧ p1)))) ∨ (True ∧ (((p2 ∧ p4) ∨ (p3 → (((False ∧ (p1 ∧ (p2 ∧ p1))) → p5) ∨ p2))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42029355423151114390299015316 : ((((p2 ∧ p2) ∨ ((p1 ∧ ((((p3 ∧ False) ∧ p5) ∨ p1) → (True ∨ ((False ∨ p4) → p2)))) ∨ (True ∧ (p5 ∨ (p4 ∨ p1))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233891427746805007404314412904 : ((p4 ∨ (p3 ∨ p2)) → (((p2 ∨ (p1 ∨ ((((p4 ∨ (((p1 ∨ p4) → (False ∨ True)) ∨ p3)) ∧ (p2 ∧ p1)) → p3) ∧ p4))) → False) ∨ True)) := by
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
theorem thm_5_vars_254392884435666641808437085403 : ((p2 ∧ p5) → ((((p2 ∧ p3) ∨ (True ∨ p4)) ∧ (p1 → (((True ∧ p3) → p4) → ((p5 ∧ (((p5 ∧ p5) ∧ False) ∨ p4)) ∧ True)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301084282069018771011588015248 : (False ∨ (((((True ∧ True) → p5) ∨ p4) ∧ (p5 ∧ (p1 → True))) → ((p3 ∨ p2) → (True → (p4 → (p1 → (p4 ∧ ((False ∧ p5) ∨ p5)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h17.left
      let h23 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h1.left
    let h26 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h26.left
      let h32 := h26.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h31
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h1.left
    let h35 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h35.left
      let h41 := h35.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137297882651293876987898281423 : ((p2 ∧ ((p5 → ((((True → ((p1 ∧ p2) ∨ (p4 → p5))) ∨ (p4 → (p2 ∨ p5))) → p1) ∧ (False → p3))) → False)) ∨ (False → (p1 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653429079085480162994821594330 : ((((p4 → ((p1 → (p5 → (False ∨ (False → ((p3 → p4) ∧ (p5 ∧ (((p1 ∧ (p2 ∨ p3)) ∨ p2) → True))))))) → p5)) ∧ (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43953732827842124426336699005 : (((((p5 ∨ p4) ∨ (((p1 → (False ∨ (((False → (p1 ∨ p4)) ∧ p2) → p1))) → (p2 ∧ p1)) → (True → False))) ∨ (p4 → p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702199739670933911161259938846 : ((((((p3 ∧ ((p1 → False) → (p5 → p5))) ∨ p5) ∧ p1) ∨ (((((False ∧ True) ∧ p1) ∨ (p5 ∨ (True ∨ p5))) ∨ p3) ∧ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86002475293723952014797784573 : (((((True → p2) → p5) ∧ (((p1 → True) ∨ p1) ∧ p2)) ∧ (((True ∧ p4) ∨ False) → (p3 ∧ ((p1 ∧ (False → (p3 ∧ p5))) ∧ p1)))) → p2) := by
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
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217010666723808164704704776448 : ((((p1 ∧ p1) ∧ True) ∨ p1) → ((((True ∨ ((p5 ∨ (p3 ∨ p1)) ∨ (p1 ∨ p3))) → p5) → (((p3 ∧ True) → p4) ∨ (p4 ∨ True))) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664466352461827108321763946626 : ((((p4 ∨ (((p2 → (((p1 ∧ p3) ∧ (True ∨ (False ∨ (((False → True) ∧ p1) → p3)))) → p4)) ∨ False) → (p2 → p4))) → (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190763267023736153105018290604 : ((((((p3 ∧ p3) ∨ p3) ∧ p4) ∧ p3) ∨ (p5 → True)) ∨ (p1 ∧ (((p1 ∧ p2) → (((False ∧ (True ∨ (p5 → p5))) ∨ p4) ∨ p4)) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207771984572855954743797498209 : (((p3 ∨ (False ∨ (True → True))) → False) → ((p3 ∨ (p4 ∧ (p2 ∧ p2))) ∧ ((p4 → (((p5 ∨ ((False ∨ True) ∧ p3)) → p3) ∧ p3)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (False ∨ (True → True))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ (False ∨ (True → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43843875287492060738075065465 : (((((False ∧ (((((p2 ∧ p3) ∨ p1) ∧ (p5 ∧ (((p1 → p3) ∨ (p1 → p5)) → p5))) ∨ p2) → True)) → True) ∧ (p5 ∨ p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253864221259391225343492188981 : ((p1 ∧ p3) → (((p1 ∧ (((p4 ∧ ((p4 → False) ∨ p5)) ∧ p1) → ((p4 ∨ p5) → False))) ∧ p2) ∨ (True ∨ (((p5 ∨ p1) ∨ p2) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186302475270498974265631935712 : ((((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) → False) → (p2 → (((p3 ∨ (p2 → p3)) ∨ p1) → (p4 ∧ (p3 → (p1 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h6
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h10
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h23 := h1 h21
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h25 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h25
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h29 : ((p5 → (p1 → (((p3 ∨ p1) ∨ p3) → p1))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h29
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169438935956199540276427954101 : ((((((p1 ∧ (p2 ∧ p2)) → p2) ∨ (p4 ∨ (p4 ∧ p2))) → (p3 ∧ p1)) ∨ True) ∧ (True ∨ (((p5 ∨ (p3 ∧ p2)) ∨ (p5 ∨ p3)) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197125575238886698036470237282 : (((p3 ∨ ((p5 ∧ p4) ∧ (False ∨ p5))) ∨ p2) ∨ ((p4 ∧ (True ∨ (p5 → False))) → (((p1 → False) → (p2 ∨ p4)) ∨ (p1 ∨ (p4 → False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258842680781550242492027681995 : ((True → p1) → (((p2 → p5) → (p3 ∧ (((p4 ∨ ((True ∨ (p5 → p2)) ∨ p5)) ∧ (p5 ∧ p1)) → p5))) ∨ (True → ((False ∧ p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62939207798978556792409369854 : ((p4 ∧ (p3 ∧ (False ∧ ((((p3 → p3) ∧ p3) ∧ p4) ∧ (p4 ∨ ((p4 ∨ p4) ∧ (p2 ∧ (p2 ∨ ((p2 → p1) → (p1 ∧ p2)))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345297079774586419714992079882 : (p3 → ((p3 → ((((p2 ∧ p2) ∨ (((p1 ∧ p2) ∨ False) ∨ True)) ∧ (p4 → (p1 ∧ (p1 ∧ False)))) ∨ ((True ∧ (p4 → p4)) ∨ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172320520063704533874118909542 : (((((p3 ∧ (p2 ∨ p4)) ∧ p5) ∧ p5) ∧ ((False → ((p4 ∨ True) ∨ p3)) ∨ p3)) ∨ (((p4 ∧ (p1 ∧ ((p3 → p3) → p3))) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311754307968649803645447763396 : (p2 ∨ (False ∨ (((((p2 ∨ p2) → (p2 → ((p3 ∧ (p2 ∨ ((p5 ∨ (p3 ∨ p4)) ∨ False))) ∧ p4))) → (p4 ∨ p2)) ∨ p3) ∨ (p3 → True)))) := by
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
theorem thm_5_vars_167513804361590090290329455498 : (((((p4 → False) ∧ p1) ∧ (((p5 ∨ (p3 ∨ (p3 ∧ p3))) ∧ p1) → p5)) ∧ (p2 → p3)) → ((p4 → ((p3 ∨ p3) → p2)) ∨ (False ∧ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62708371983859577525841344536 : ((p4 ∧ ((((p2 → False) ∧ p5) ∨ ((p3 ∧ ((True → p5) ∨ ((p4 ∨ p4) ∧ (True ∧ p2)))) ∧ (p5 ∨ (p1 ∧ (False ∧ p5))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185320392877529859462429961534 : ((p3 ∧ ((p1 ∨ ((True ∧ p3) → p1)) → ((p1 ∨ False) ∨ True))) ∨ ((((p2 ∧ ((p4 ∧ (p5 → True)) ∧ True)) ∧ True) ∨ p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52038057894043483251927740238 : (((p5 ∨ ((((p5 ∧ (p3 → True)) ∧ (True ∨ p4)) ∨ False) → (p4 ∨ (p1 ∧ False)))) ∨ ((p4 → (((p4 ∨ p4) ∨ p4) → p4)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48953879670589915520595021939 : ((((p3 ∨ ((p2 ∧ (p1 → (p4 ∨ False))) ∨ ((p5 ∨ ((p4 ∨ True) ∨ p1)) → (p2 ∧ (p2 ∨ False))))) ∧ p3) ∨ (False → (p2 → p5))) ∨ p5) := by
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
theorem thm_5_vars_111333468365434805663815226044 : (((p2 ∧ (p2 ∨ ((((((((False ∧ (p1 ∨ ((p4 ∧ True) → p4))) ∨ p5) ∧ p5) ∨ p4) → p2) ∨ p4) → p2) ∨ p2))) ∧ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748642809619340876502400851832 : ((((p3 → p2) → ((p4 ∨ p2) → ((p2 ∨ ((True → False) ∨ ((((((p2 ∧ p2) ∧ p4) ∧ p1) → True) → (p5 → True)) → p1))) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737923311444192419685858611130 : ((((True ∧ p3) ∨ (((True → (((p3 ∨ (False ∧ (p4 ∧ ((False → p5) ∨ (p5 ∨ False))))) ∨ False) ∨ p3)) ∨ True) ∨ (p1 → (p1 → False)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_51171793349590196492840297611 : (((((p4 ∨ (p3 ∨ p2)) ∧ ((p2 ∧ (((p5 → p1) ∧ False) ∧ p5)) ∧ p1)) ∨ (p2 ∧ p1)) ∨ (p5 ∧ ((p2 → False) → (p3 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117743691227769036984378033874 : ((p4 ∧ ((p5 ∨ (p3 ∧ ((((((True ∨ False) → p3) ∧ ((p1 ∧ p1) ∨ p2)) ∨ p4) → (True ∧ (True ∧ True))) ∧ p2))) ∧ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258434665297149746462099423740 : ((p5 ∨ p1) → ((p1 ∧ True) → (((p5 ∨ (p5 ∨ (False → ((p2 ∨ p3) → p1)))) ∧ (False → (p3 ∨ (p3 ∨ (p2 → p5))))) → (p2 ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h2.left
      let h14 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h2.left
      let h19 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204186939679294214173928986575 : ((((p4 → (p3 ∧ p5)) ∨ p2) ∧ p4) ∨ (True → ((p4 → (p1 ∧ ((((p5 → (p1 ∧ (p2 → p3))) ∧ False) ∧ False) ∧ (True → p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322256445232873308524699034952 : (p5 ∨ ((((p3 ∨ (p4 ∨ (p4 ∨ (p3 ∨ (True ∧ True))))) ∨ ((p1 ∨ ((p5 → p2) → p1)) ∨ (((p4 ∨ p4) ∧ True) → True))) ∨ p2) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190307796906677036126140403262 : ((((p4 → ((p4 → (False ∧ True)) ∧ p3)) → p4) ∨ True) ∨ (p2 ∨ ((((p5 ∨ p4) ∨ p4) → p3) ∧ (((p2 ∨ p5) ∧ p2) ∨ (True ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463045836961758926496916806259 : (((((((p1 → False) → (p5 ∨ p2)) ∨ p2) ∧ ((False ∨ ((True ∨ p5) ∧ True)) ∧ False)) ∨ (((p5 ∨ (p4 ∨ p5)) ∨ (True ∨ p1)) ∨ p5)) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177997550437481216017724272369 : (((False ∨ (False ∨ (((p5 ∨ ((p5 → p5) → p2)) ∨ p3) ∨ p1))) ∨ True) ∨ (True → (((p1 → True) → (False ∨ p5)) ∨ (False → (p1 ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65881069636542362249171800396 : ((p4 ∨ ((True ∨ False) → (((p4 ∨ (((p4 → p3) → p5) → p3)) ∨ p5) ∧ ((((p3 ∧ True) → False) ∧ ((False → p1) ∧ p2)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692606952285784835646861054541 : (((((((p5 ∧ False) → (p3 ∨ p1)) → (p1 ∧ p2)) ∨ ((p4 ∧ True) → p4)) ∧ ((p2 ∨ True) ∧ (((True ∨ False) ∨ p5) ∨ (p4 → p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257055106469119007186074986912 : ((p2 ∨ True) → (p4 → ((p3 ∧ p1) ∨ ((p4 → (((True → (((p1 → p1) ∧ p4) ∧ p4)) ∧ (False → True)) → p3)) ∨ (p4 ∨ (True → p2)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148543680365363892023207152580 : (((p4 → (p3 → ((p3 ∨ p5) ∧ ((p3 ∨ (p3 ∨ p5)) ∧ p2)))) → (p3 → ((p3 → p5) ∧ (p2 ∨ False)))) ∨ (False → (p4 → (p1 → p2)))) := by
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
theorem thm_5_vars_722830120450643099838173637617 : (((((False ∧ p4) ∨ p2) ∧ (True ∧ (((p4 ∨ ((p1 ∧ p4) ∧ ((p2 ∧ (p3 → p3)) → (p4 ∨ True)))) ∨ ((p2 ∨ p3) ∧ p3)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259512478665228876740492157752 : ((False → p5) → ((p1 ∨ (False ∧ (p2 ∨ (True ∧ ((p4 ∧ p1) ∧ (((False ∨ False) ∨ p3) ∨ p2)))))) ∨ (False ∨ ((p4 → (False → p3)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47524889636949997028804826077 : (((p3 ∨ (p4 ∧ (((True ∨ ((p5 ∨ (p2 ∧ p5)) → p5)) ∨ p2) ∧ ((p2 ∨ p1) → ((False ∨ (p5 ∨ False)) ∧ p4))))) ∨ (p2 → p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233881473303594572672282011458 : ((p4 ∨ (p1 ∨ p3)) → (True ∧ (((((p4 ∨ p5) → True) ∧ True) ∧ ((True ∧ p3) ∧ p5)) → ((((False ∨ p4) ∨ (p3 ∧ False)) ∨ p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115728533690194132824983910553 : (((((True → p5) ∨ p3) ∧ (p2 ∧ p5)) → (False ∨ ((((p1 ∨ p3) ∨ p5) → (False ∨ True)) ∧ (((p2 ∧ p1) ∨ p3) → p2)))) ∨ (p4 ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- Implications on the right can always be decomposed.
    intro h25
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h29 =>
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43878467074581551092512363511 : (((((p3 ∨ p4) → ((p5 ∧ p4) → (p1 → (True ∨ (p2 ∧ ((False ∨ ((p2 → (p3 ∨ True)) ∨ p3)) → True)))))) ∧ (p5 ∨ p3)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748994423499110325950709405319 : ((((p4 → p4) → ((False ∧ True) ∧ ((((((p5 ∧ p4) → (p2 ∧ (((True ∧ p5) ∨ (True ∨ p2)) ∨ True))) ∨ p3) → p4) → p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655571614266939069863026680166 : (((((((True ∧ p3) ∨ (p1 → p4)) ∧ ((((True → (p2 ∨ (p3 ∨ p3))) ∨ (p5 ∨ p5)) ∧ p5) ∧ p2)) → (p1 ∨ p1)) ∨ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41244682332060009241167888618 : (((((p5 → (p1 ∧ (p4 → (p2 ∨ ((p3 ∧ (p3 ∧ ((True ∨ False) ∨ p2))) ∨ False))))) ∧ p2) ∨ ((p3 → False) ∨ (p3 → p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111261403798750242844942382345 : ((((p5 ∨ p2) ∨ ((p4 ∨ (((True ∧ (False → p1)) ∨ (p2 → p1)) ∧ p2)) ∨ (p1 ∧ ((p4 ∧ (p1 → p2)) ∧ p2)))) ∧ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349425096385051828881758525472 : (p3 → (p4 → ((p4 ∧ (p3 ∨ p1)) ∧ ((((p5 ∨ (p1 ∨ False)) → p4) → False) ∨ (p5 ∨ ((p2 ∨ (((p2 ∨ p1) → p1) → p2)) ∨ True)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53619069856543978992333401371 : (((((p4 ∨ (p4 ∨ p4)) → (True ∨ p1)) → (p5 ∨ False)) ∧ (False ∨ (True ∧ ((((p1 → p4) → False) ∧ (True ∧ False)) ∨ (p4 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117023912534992691894892666779 : (((p2 ∨ False) → ((False ∧ ((p5 ∧ p1) ∨ ((p5 → False) → (p1 ∨ (((((p1 → p1) → False) ∧ p2) ∧ p2) ∨ p2))))) ∨ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158055068781786141203475150132 : (((p2 ∧ (((True → False) → True) ∧ False)) ∨ (p2 ∨ ((False → p5) → ((False → (p2 → p3)) ∧ p4)))) ∨ ((p2 ∨ p2) ∨ (p1 → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347485181522799847153424130003 : (p3 → (((p2 → (True ∨ p4)) → (False ∧ p3)) ∨ (((False → True) → (False ∨ (False ∧ p4))) → (((p1 ∧ (False → False)) ∨ (False ∨ p5)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
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
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225523688799183273582158239003 : (((True → True) ∧ p1) ∨ ((((p3 → ((p5 ∧ (p4 → (p3 → p3))) ∨ True)) ∨ False) ∧ (p3 ∨ p3)) ∨ (p4 → (((True ∨ False) ∧ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119423016298235423087217651655 : ((p4 → ((p3 → ((True ∧ (p5 ∧ p1)) ∨ ((p2 ∨ (p4 ∧ p4)) ∧ (True ∧ (p3 → ((p3 → p5) ∧ p4)))))) ∧ (p5 ∨ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259821110713443177783300458593 : ((p1 → p3) → ((p5 → ((p1 ∨ p3) ∨ (True ∨ (p2 → p4)))) ∧ ((((False → (p5 → p4)) ∧ p3) → p4) ∨ (((p2 ∧ False) → p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322468203691249920345730734282 : (p5 ∨ (((p5 ∧ (p1 → p5)) → (((((True → (False ∧ p5)) → p5) → False) ∨ (p2 ∨ p5)) ∨ ((((True ∨ p3) ∧ p4) → False) → p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_682960500374405248175077486526 : (((((p1 → False) ∨ ((True ∨ (p2 ∧ (p1 → ((False → ((p3 → p1) ∨ False)) ∨ False)))) → p1)) ∧ (p3 ∧ (p2 → (p1 → (p1 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161007834000600125967492412007 : (((True ∧ (p3 → p4)) ∨ (((p4 ∨ p2) ∨ (True ∨ ((p5 ∨ (False ∧ (p4 ∧ p4))) ∨ True))) ∨ p3)) → (((True → p1) ∨ p3) → (p3 ∨ p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h13 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h14 := h3 h13
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h16 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h17 := h3 h16
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h20 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h21 := h3 h20
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- Disjunctions on the left can always be decomposed.
              cases h23
              case inl h24 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                have h25 : True := by
                  -- True on the right can always be proven directly.
                  apply True.intro
                -- We have shown the premise of h3, we can now drive its conclusion.
                let h26 := h3 h25
                -- One of the premise coincides with the conclusion.
                exact h26
              case inr h27 =>
                -- Conjunctions on the left can always be decomposed.
                let h28 := h27.left
                let h29 := h27.right
                -- False on the left can always be used.
                apply False.elim h28
            case inr h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
              have h31 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h3, we can now drive its conclusion.
              let h32 := h3 h31
              -- One of the premise coincides with the conclusion.
              exact h32
      case inr h33 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h42 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
        case inr h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h45
            case inl h46 =>
              -- Disjunctions on the left can always be decomposed.
              cases h46
              case inl h47 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h34
              case inr h48 =>
                -- Conjunctions on the left can always be decomposed.
                let h49 := h48.left
                let h50 := h48.right
                -- False on the left can always be used.
                apply False.elim h49
            case inr h51 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h34
      case inr h52 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652625389038854212852368760136 : ((((False ∨ (p2 ∨ (((False → p5) → False) ∨ ((p5 ∨ ((p2 ∧ (p2 ∧ p5)) ∨ (((False → p2) ∨ p4) → p4))) ∧ p4)))) ∧ (p4 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205141229831172574260324278716 : ((((True → p1) → p3) ∧ (p2 ∨ p2)) ∨ (((p2 → (p3 ∨ ((((p3 → True) ∧ p1) ∧ p5) ∧ p4))) ∧ ((p1 → (p2 ∨ p1)) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229861470140992817254300929467 : ((p5 → (False ∨ p4)) ∨ (((((p4 ∧ p4) ∧ p3) ∨ True) ∨ ((True → (p3 → ((p2 ∧ p4) ∨ True))) → (p1 ∨ p2))) ∨ (True ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113056271947281295116492620877 : (((p2 ∨ ((p4 ∧ (p4 → ((((p4 ∧ True) ∧ ((False ∧ p2) ∧ (True ∧ ((p5 ∨ p4) → p2)))) → False) ∨ False))) ∨ p2)) → p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157941266914144080348063222059 : ((((p2 ∧ p4) → (((p5 ∧ p5) → p2) → p4)) ∧ ((p1 ∧ (p4 ∨ (p4 ∧ p3))) ∧ (p3 → False))) ∨ ((False ∧ p5) → ((True ∧ p3) ∨ p2))) := by
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
theorem thm_5_vars_669983444865962250674903802613 : ((((((p3 → p4) ∧ ((p5 → (p3 ∨ (p4 ∨ p3))) → False)) → (p2 ∧ (p2 → (((True → p4) ∨ p4) → p1)))) ∨ (True → (False → p1))) ∨ False) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179434548594973701772171652539 : ((p4 ∨ (p4 ∨ ((p3 → (((p4 ∧ (False ∨ p4)) ∨ p4) ∨ True)) ∨ p4))) ∨ (((p2 ∧ (True ∨ p2)) ∨ p3) ∧ ((p2 → p1) ∧ (p3 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781436043505087564492909180100 : (((p2 ∨ (p4 ∧ (((((p4 → p2) ∨ ((p3 ∧ (p4 ∧ p4)) ∨ p5)) → p4) ∨ ((p1 → (((p5 ∨ p2) ∧ p3) ∧ True)) ∧ True)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329352738115456535468821336553 : (True → (((p2 → False) → p5) → (((False ∨ (False → (p3 → (p4 ∧ p1)))) ∧ ((p5 → (p1 → p2)) ∨ p3)) → ((p2 ∧ (p3 ∨ p1)) ∨ True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
theorem thm_5_vars_191620351337429310197303528686 : ((p3 ∧ (p4 ∧ ((((False ∨ True) ∧ False) ∨ p4) ∧ p5))) ∨ (((((((p5 ∧ (p3 ∨ p1)) ∧ p1) ∧ p5) ∨ p5) ∧ (p2 → p3)) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115652538807086237334668549434 : (((((p4 ∧ p5) ∨ p2) ∧ (p1 ∨ p3)) ∨ (p2 ∨ ((((p1 ∧ True) → p5) ∧ False) ∧ (True → (p1 ∨ (False ∨ (False ∨ p3))))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



