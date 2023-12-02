variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191907887940624548478445292666 : ((p5 ∨ ((p1 ∨ p1) ∨ (((False ∨ p2) ∧ False) ∧ p5))) ∨ (((False → (((True ∧ p2) ∨ p2) ∨ p3)) → ((True ∨ False) ∧ (True ∧ p4))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (((True ∧ p2) ∨ p2) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135872532392109152474573106481 : ((((True → (False → (p2 ∧ p4))) → ((p2 → (p3 ∧ p3)) ∧ True)) ∨ ((p1 ∨ ((p5 ∧ p4) ∧ (False → p1))) ∨ True)) ∨ (True ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251125886653467624948442739847 : ((p2 → False) ∨ ((p2 ∧ (((p2 ∧ (p1 ∨ True)) → p4) ∧ (True ∧ ((p2 → p1) → (p1 ∧ ((p4 ∧ p5) ∧ (p2 ∨ p4))))))) → (p4 ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∧ (p1 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312385828048922961483703642909 : (p2 ∨ (p3 → ((True ∨ p4) → (((((p2 ∨ p2) ∨ False) ∧ (p5 → (p2 → (p3 ∨ (p5 → p4))))) ∨ p3) ∨ (p2 ∨ ((p4 ∧ True) → False)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232285041312256259548168615437 : (((p2 → p4) → p4) → (((((p5 ∨ ((True ∨ True) ∨ p2)) ∨ (p3 ∧ (p2 ∨ ((p3 ∨ False) ∧ p4)))) → p3) ∨ p2) → ((p4 ∨ p1) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764809023397069188529407941119 : (((p4 ∧ ((((p4 ∧ (True → ((p5 ∧ (False ∧ (p5 ∨ ((p4 ∨ p3) → (p1 → (False ∨ (p1 ∨ p5))))))) ∨ p3))) ∨ p4) → p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114735152222951754373988638738 : (((((p3 → (p4 → True)) → p5) ∨ (((p1 ∨ p1) ∨ (p3 ∧ p3)) → (p1 ∧ p4))) → (((p4 → p5) ∧ p5) ∧ (p4 ∨ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64840705475413478666284966051 : ((p2 ∨ ((p3 ∧ (p5 ∨ (p5 → ((((p1 → (True ∨ ((p4 → (p4 → p2)) ∨ p4))) ∧ p2) ∨ ((False → p4) ∨ p4)) ∧ p5)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42949842218217167503256696188 : (((p4 → (p4 ∧ (((((p1 ∧ p1) → p2) ∨ False) → (p3 ∨ ((p3 ∧ ((p5 ∨ (p5 ∨ p1)) ∧ p5)) ∨ True))) ∨ (p5 → p5)))) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354361321598313423445607278365 : (p5 → (((((False → ((p1 ∧ p4) ∧ True)) → p5) → p2) → ((False ∨ p4) ∨ ((((p4 ∧ (True ∧ p3)) ∧ p2) ∨ (p4 ∧ p5)) ∨ p2))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False → ((p1 ∧ p4) ∧ True)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134119105099777903261697974941 : ((((((((((p1 ∧ p5) ∧ p4) ∨ p2) ∨ True) → p4) → ((p5 → (False → p4)) ∨ False)) → p4) ∨ (p4 → p2)) ∨ True) ∨ (p4 ∧ (True ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112555627337319105470386094813 : (((((p3 ∨ True) ∨ ((p3 ∧ ((p1 ∧ ((p3 ∧ p2) ∧ (p1 ∧ (True ∨ (False → p3))))) → p3)) ∧ (p1 ∨ p4))) → p1) → p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112816741816975270746500848066 : (((((p5 → (p3 ∧ p2)) ∨ p1) ∧ ((p4 ∨ ((p4 → p3) ∨ p3)) → (((False ∨ (p1 ∨ p4)) → (p1 ∨ False)) → p2))) → p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89049156468307244674491615615 : ((((p5 → p4) ∧ p1) ∧ (True → ((((p3 ∧ p4) → p5) ∨ (p4 → p1)) ∧ (True ∧ (p5 ∨ (p5 ∧ ((p3 ∨ (False ∨ p3)) ∧ True))))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137159927546455709489951779087 : ((False ∧ (((p4 ∧ (p4 → ((p4 ∨ p5) → ((p2 ∧ (((True ∨ p1) ∧ p5) ∧ (True → True))) ∨ p4)))) ∧ p2) → p5)) ∨ (True ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2184056399269111784391118067 : (((((p1 ∨ (p1 ∧ p3)) → ((p2 → p1) ∨ (True → False))) → p3) ∧ (p4 → False)) ∨ (p4 ∨ (((p3 ∧ False) ∧ p5) → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52769068144295332894456776137 : ((((p2 ∨ ((((p4 ∨ False) ∧ False) ∨ ((p2 ∧ False) ∧ p5)) ∨ p3)) → False) → (p3 → (p2 ∧ ((True ∨ p1) ∧ ((p2 ∧ False) ∨ p3))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ ((((p4 ∨ False) ∧ False) ∨ ((p2 ∧ False) ∧ p5)) ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166293607733520798990276961045 : ((p4 ∧ ((p1 ∧ (p2 → (p1 ∨ p3))) ∨ (p5 ∨ ((p2 → ((p5 ∧ p1) ∨ p5)) → p1)))) ∨ (False ∨ (((p1 ∨ (p2 ∨ p5)) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41425552926872816069974596622 : (((((((p3 → p5) ∧ False) → (True ∨ (p1 ∨ (p3 ∨ (p4 ∧ False))))) ∧ p1) → ((p1 → False) ∧ (((True → True) → p5) ∧ p1))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53650326080863387716660615369 : (((((False ∧ p3) ∨ p4) → ((p3 ∨ (False ∧ p4)) ∧ True)) ∧ (((((False ∨ p1) → True) ∧ p3) ∨ (p2 ∨ (False ∨ (p4 ∧ p1)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230748139901075718629063840361 : (((p5 → p4) ∧ p2) → ((p1 ∧ (((p4 ∨ (p1 ∨ ((p1 → p1) → p4))) ∨ ((p1 ∧ False) → (p2 ∨ (True ∧ (True ∨ False))))) ∧ True)) ∨ p2)) := by
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
theorem thm_5_vars_258722930954397232401743687421 : ((True → True) → ((False ∧ (((p5 ∧ p1) ∧ (p5 ∧ ((p5 → ((p3 → p1) → True)) ∧ p5))) ∨ p4)) ∨ ((p1 ∧ ((True ∧ True) ∨ p4)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174721063067831115396976667259 : ((((p5 ∧ p5) ∧ True) → (((p4 ∨ (((p4 → p4) ∧ p5) ∧ False)) → p2) → True)) → (((p3 → False) ∨ p4) ∨ (((p3 → p1) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134751882433093306968687297594 : ((((False → True) ∨ (True ∨ (((((False ∨ p5) → p4) → (p1 ∧ (p4 ∨ p5))) ∨ p5) ∧ ((p1 ∨ p2) ∨ True)))) → p4) ∨ (p4 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165219834632721235688627684745 : (((((p1 ∨ p3) → ((p1 → p2) → p5)) ∧ (((p1 → p5) ∨ p3) ∨ p4)) ∨ (p4 → p4)) ∨ ((p3 ∧ (p4 ∨ False)) ∧ (p5 ∨ (p4 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148012958154386672842321581087 : ((((((p4 ∧ p4) → True) → (((True ∧ p5) → True) → (p1 ∧ p3))) ∨ (p5 ∨ (p1 → True))) ∨ (True → False)) ∨ (((p4 ∧ p1) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305408185920174553867612329166 : (p1 ∨ (((p1 → (p5 → (False ∧ (False → False)))) ∨ ((p3 ∨ ((p3 ∧ p1) ∨ True)) ∨ p5)) ∨ ((p1 ∧ ((p3 ∨ True) ∨ (p4 ∧ True))) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_68159996985808322689167582782 : ((p3 → (((False → p2) → ((((p1 ∨ (((p1 ∨ p1) → False) ∨ p1)) ∧ p1) → (p1 ∨ (True ∧ p5))) → (True ∧ (p5 ∨ p2)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259821859603129857432024847747 : ((p1 → p3) → (((True ∨ False) → ((p4 → (p4 ∨ False)) ∧ True)) → ((((p1 ∧ ((False ∨ (p1 → (p4 ∨ False))) ∨ p4)) ∨ True) ∨ p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179408514052033861029484558253 : ((p3 ∨ (p4 → (p1 ∧ ((p2 → ((p1 ∧ p4) ∨ p3)) ∧ (p5 ∨ p1))))) ∨ ((p2 ∧ p2) ∨ (p2 ∨ ((False → ((True ∨ p1) → False)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225051085176048336749803521178 : (((p1 ∧ True) ∧ p1) ∨ ((((((p5 → (True → p5)) → (True → ((True → p3) ∨ (p3 → p2)))) → p4) → (True → p2)) ∨ (p2 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645079293589017881047493852673 : ((((p3 ∨ ((((((p1 ∧ (p3 ∧ (p4 ∨ (p1 ∧ ((True ∨ False) → (False → p5)))))) ∧ p2) ∨ False) → p1) ∧ (p5 ∨ p4)) → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313982499813198166769225697318 : (p3 ∨ ((((False ∨ False) → ((p2 ∨ p3) ∨ p2)) ∧ (((p2 ∧ (p4 ∧ True)) → (p2 ∨ (p4 ∧ p3))) → ((p1 ∧ p5) ∨ p5))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61126942353146155880330936391 : ((False ∧ (((p2 ∨ ((p4 ∧ p2) → (False ∨ p2))) ∧ p3) ∧ ((((p5 ∨ (False → p4)) ∨ (p2 ∧ ((p2 → p5) ∧ p5))) ∧ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769710913738416516196712209653 : (((p5 ∧ (p1 ∨ (p1 ∧ (((p5 ∨ (((p3 → (p2 → (p4 ∨ ((p4 ∧ False) → (p3 ∨ False))))) → p5) ∧ p3)) ∨ p3) → (p4 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204230981523867257837971482667 : ((((p4 → (p5 ∨ p4)) → False) ∧ p4) ∨ (((p1 → (True ∨ ((False ∧ (p2 ∧ True)) ∨ (((p5 ∧ p5) → p5) ∨ (False ∨ False))))) → False) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (True ∨ ((False ∧ (p2 ∧ True)) ∨ (((p5 ∧ p5) → p5) ∨ (False ∨ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135870533051313986472730044534 : ((((((p3 ∧ p3) → p5) → False) ∧ ((p1 → (p5 ∨ p4)) ∧ p2)) ∨ (False ∧ ((((False ∧ False) ∨ p1) ∨ p4) → p2))) ∨ ((True ∧ False) → False)) := by
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
theorem thm_5_vars_149923090069493088595853320932 : ((p3 ∨ (((p2 ∧ p3) → (((p5 ∨ ((p1 ∧ True) ∧ (p5 ∨ p5))) ∨ False) ∧ p1)) ∧ (p2 ∨ (False → p3)))) ∨ ((True ∨ (p5 → True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172709869605016536862359019737 : (((p2 ∨ p2) ∨ (((p5 ∨ p3) → (p4 ∨ (True ∨ ((False ∨ p5) → p3)))) → p3)) ∨ (((False ∨ False) → p1) ∧ (False → (p5 ∨ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207196277590376095617333852489 : (((((p2 → False) → p2) ∧ True) ∨ p3) → ((p4 ∧ (True → ((p1 ∨ False) ∧ p3))) → ((p3 ∨ (p1 ∨ p2)) → ((p5 ∧ (p5 ∧ False)) ∨ p3)))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
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
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h19 := h14 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h2.left
      let h24 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h29 := h24 h28
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41748804853468340048420373038 : (((((p3 ∧ (p4 ∨ p5)) ∧ False) ∨ ((True → ((((((True ∨ (p4 ∧ p5)) → False) ∧ p3) ∨ p2) → p1) ∧ (True → True))) ∨ False)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65290946055184761225279352752 : ((p3 ∨ ((((p5 ∨ p4) ∧ (True → ((p3 ∧ p5) ∨ p5))) ∨ ((((p5 ∧ False) → True) → ((p1 ∧ p4) ∨ p2)) → True)) ∨ (p3 ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156594063888868387270580065718 : ((((((((p1 ∧ True) → (False → p3)) ∧ (False ∨ ((p4 ∧ p2) ∨ p3))) ∧ p1) ∨ p4) ∧ False) ∧ p5) ∨ ((p2 ∨ (p1 → (True ∨ p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201254525318138439532822081838 : ((p3 → ((False ∨ ((p2 ∧ True) → False)) → p2)) → (((((p1 ∨ p5) → True) ∨ (False ∧ ((p3 → p2) ∧ p5))) → p5) ∨ (p5 → (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246147197848179750262694504376 : ((p4 ∧ p2) ∨ ((p3 ∨ ((p1 ∨ ((p3 → False) → p2)) ∨ (p1 → ((p4 ∨ (False → ((True ∨ True) ∨ p3))) ∨ p3)))) ∧ ((p3 ∨ True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70939424882373183066747449441 : ((((((((False → (True ∨ p3)) ∧ p3) → False) ∧ p3) ∨ True) → (False ∧ (False → (((True → ((p2 ∧ p4) ∧ p3)) → False) → p4)))) ∧ p5) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((False → (True ∨ p3)) ∧ p3) → False) ∧ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225324231440267535581521853686 : (((False ∨ p5) ∧ p5) ∨ (((p3 ∧ (p2 ∧ p2)) → ((p5 → (p4 ∧ p2)) → ((((p2 ∧ p4) ∨ p5) ∧ True) ∨ ((True ∨ p4) ∧ p2)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134274042894390526375524751378 : ((((p2 ∨ p5) ∧ ((p1 ∨ (True ∧ (p5 ∨ ((p2 ∧ p3) ∧ p5)))) ∨ (p3 ∧ ((p4 ∨ (p2 ∨ p2)) → p5)))) ∨ True) ∨ ((p1 ∨ p4) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330321262923348671476101753579 : (True → (p1 ∨ (((((p1 ∧ p5) ∨ p3) ∨ (False → p4)) → p3) → ((p3 ∧ ((p5 → ((p5 ∧ False) → (p1 → False))) → p3)) ∧ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ p5) ∨ p3) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (((p1 ∧ p5) ∨ p3) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206731853781099957744352183776 : ((p3 → ((p1 ∨ p5) ∨ (False ∨ p5))) ∨ ((((p5 ∧ ((p4 ∨ p3) ∨ ((p2 ∨ p4) ∧ p5))) → (p2 ∨ (p3 ∨ False))) → p4) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187654708249093911326871206782 : ((True → (((((p2 → False) ∨ p5) → p5) → (p3 ∨ p3)) ∧ p5)) → ((p5 ∧ (p1 → ((((p4 ∨ True) ∧ p1) ∧ p5) ∨ (p2 ∧ p4)))) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85466099339869776270756853940 : (((True → ((p3 → (p4 → False)) ∧ (False ∧ (False ∨ (True ∨ True))))) ∧ (True ∨ ((((p2 ∨ p1) → p4) ∧ p3) → ((p5 ∧ True) ∨ p1)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45910241282695486064690294469 : (((p4 → ((p3 ∧ ((((p3 → (True → False)) ∨ (p5 ∧ (True → p5))) ∧ (p4 ∧ True)) ∨ (p5 ∨ p5))) → ((True ∨ p3) → p5))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136445481272424465116455073908 : (((p1 ∧ (False → (p2 → p1))) → ((p2 → (p3 ∧ p5)) ∧ ((p4 ∨ ((p3 → ((p3 → p2) → p3)) ∧ p3)) ∨ True))) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110964642330724946266492732589 : (((((p5 → True) → ((((((p1 → ((p5 ∧ (p5 → p2)) ∧ p1)) ∧ True) → p2) ∧ p4) ∨ p2) ∧ p1)) ∨ (p5 → p5)) ∧ p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134876545845292668492921163895 : (((p2 → ((p2 ∨ (((p5 ∨ ((True ∨ p5) → p4)) ∨ (True ∧ p1)) ∧ p1)) → (((p3 → p1) ∨ p1) ∨ p5))) → p4) ∨ (True ∨ (p3 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46829895850150087651396135771 : (((((False ∧ (True ∧ (((p2 ∨ p2) ∨ p4) ∧ ((p2 ∨ ((p1 → True) ∨ False)) ∨ p1)))) ∨ (p2 → (True → True))) ∧ True) ∨ (p5 ∧ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608328430382506304376677994033 : (((((((((p1 ∨ True) ∨ p3) ∨ p4) → (((((False ∧ True) ∧ (True → ((True → False) ∧ p4))) → p2) ∨ True) → p5)) ∨ p4) ∨ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_676870477875077553611990947123 : ((((p4 ∨ ((((((p2 → p5) → (True ∨ ((p3 ∨ p4) ∨ (True → False)))) ∧ p3) ∨ p3) ∨ p5) → p3)) ∧ ((p4 ∨ (True ∧ p3)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67756973626249877275452891811 : ((p2 → (((p1 → (((p4 ∨ p5) → (p5 → ((False ∧ (p5 ∨ ((p1 ∧ (p5 → p5)) → p4))) ∧ p1))) ∨ (p1 → True))) → p1) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178598343671226648169685793263 : ((((p5 → (p3 → p5)) → (False ∧ p4)) ∨ (p2 → ((p1 → p3) ∨ True))) ∨ ((p2 → p1) → ((p2 ∧ True) → (False ∨ (True → (p4 ∨ False)))))) := by
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
theorem thm_5_vars_156879562167402383108497215735 : (((((((p1 ∨ ((False ∧ p2) ∧ False)) → p5) → (((p5 → p1) ∧ p4) ∧ True)) ∧ True) ∨ p5) ∨ p1) ∨ ((((p3 ∧ p5) → p5) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655788611403486682877581913143 : ((((((p1 → p2) → ((p3 ∧ (p2 ∧ ((p4 → False) ∨ ((p2 ∨ (True → p4)) → True)))) → p5)) ∨ ((p1 → p1) ∨ False)) ∨ (p5 ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136207315753199498957337756825 : (((p5 ∨ (p3 ∨ ((True ∨ True) ∨ p1))) ∧ ((p5 ∨ (p1 → ((((p4 → (p2 ∨ p5)) → p3) ∧ p5) ∧ p2))) → p3)) ∨ (True ∨ (p5 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147927812560547673339977123511 : ((((((p5 ∨ p1) ∧ ((p4 → p2) ∨ False)) ∨ p2) → ((p3 ∨ (True → (False ∨ p3))) → p3)) ∧ (p2 ∧ p2)) ∨ (p3 → ((p2 → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322414467609541282345352033116 : (p5 ∨ (((p3 ∨ ((p5 → (p1 → (False ∨ False))) ∧ (p5 ∨ p5))) ∨ (p4 ∨ (((False ∨ p5) ∧ (p3 ∧ p3)) ∨ (True ∨ (True ∧ p3))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_117188193260343069356439339877 : ((True ∧ (((p5 ∧ ((p2 ∨ (((p2 → p3) ∨ True) ∧ (p4 ∨ False))) ∧ p2)) ∧ (p5 ∧ (p5 ∧ p5))) ∨ (False → (False ∨ p2)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54081765463497617408261542515 : ((((p4 → p5) ∧ ((p1 ∧ (p4 ∨ (False ∨ p1))) → p3)) → (((p2 ∧ p1) ∨ (((p2 → (p4 ∨ p2)) → p2) ∧ True)) ∧ (p5 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66499529593907528785555157955 : ((True → ((True ∧ (((p2 ∨ p4) → False) → ((p2 ∨ p5) ∨ ((False → (p3 → (p2 ∧ False))) ∧ ((p3 ∨ (p2 ∧ p4)) ∨ p5))))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321369684801504094782573231699 : (p4 ∨ (True → ((((p1 → ((False → (((True → (False → p3)) → True) → p2)) → (p2 ∧ (p2 ∨ p4)))) ∧ p4) → p1) → (p1 → (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155205152060805572363178238494 : (((((p1 ∨ (p2 ∨ (p4 → p5))) → False) ∧ p3) ∨ (True ∨ (False ∨ ((p5 ∨ p4) → (p4 ∨ p1))))) ∧ (((True ∨ (p2 → p2)) ∧ p5) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148516428606100660831440249962 : (((((False ∧ p5) → (p4 → ((p5 ∨ (p1 ∨ p5)) ∨ False))) ∨ p1) → (False ∧ ((p3 → p4) ∨ (True → True)))) ∨ (p1 → ((p5 → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105657417967532221155868133533 : ((((((p1 ∧ True) → p1) → False) → ((((p5 ∧ p1) ∨ p3) ∧ (p3 ∧ p4)) ∨ p5)) ∧ (False → ((p2 → False) ∨ (False ∨ p5)))) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ True) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258121233852468020203963998715 : ((p4 ∨ p3) → (((False → (p5 ∨ ((False ∨ p4) ∧ p4))) ∨ True) → (p4 ∨ ((p4 ∨ ((False ∧ (False ∨ p3)) ∨ p5)) → ((False ∨ p3) ∧ True))))) := by
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
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h20
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52553656548194363468209913781 : (((((p1 ∧ (True ∨ False)) → ((p5 ∨ (p3 ∨ (p2 ∧ p1))) → p3)) → p2) ∨ ((((p4 → p1) ∧ (p3 ∨ p4)) ∨ p5) → (False ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_96279639545451500322867164998 : ((False ∨ ((p2 → ((((p5 ∧ (p2 → p5)) → False) → (p3 ∧ (((p1 → (p4 → p5)) ∧ False) ∧ p3))) ∧ (False ∧ (p5 ∨ p2)))) ∧ p2)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65950665657862799111043483535 : ((p4 ∨ (p3 ∨ ((p3 → (((p1 → ((p2 → (p2 → ((p2 ∧ p5) ∨ p5))) ∧ p1)) ∨ p3) → ((p1 ∨ (p3 ∨ True)) ∨ p5))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51683636242722212182074085256 : ((((((p1 ∨ p4) → ((p2 ∨ (p5 ∧ True)) ∧ p5)) ∨ (False → p2)) ∨ (False → p5)) ∧ (((p3 → False) ∧ (p5 ∧ (p1 ∨ True))) ∨ True)) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213576006444750817735570782361 : ((((p4 ∨ p1) ∧ p3) ∨ p2) ∨ (((p1 ∨ p3) ∨ True) ∨ ((((True ∧ (((((p3 ∨ p2) ∧ p3) ∧ p5) → False) ∧ False)) ∨ p2) ∨ p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58081072160900932968820089227 : (((p1 ∧ True) ∧ (((p3 ∧ (p1 ∧ False)) ∨ (p2 ∨ ((p5 ∧ True) ∧ (p2 ∨ (p1 ∨ ((False ∨ p1) ∨ p4)))))) ∨ (p5 ∧ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40492165363245334375104987308 : (((((p3 ∨ True) → ((p4 ∨ p3) ∨ ((((p1 ∧ (p4 ∧ p4)) → ((p3 ∨ p2) → ((False → p4) → False))) → p3) → p2))) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53588059397946392721460159808 : (((((p1 ∧ ((False ∧ p5) ∧ p4)) → (p5 ∧ p2)) → p5) ∧ (((p2 → p2) → False) ∧ ((((p2 → (p4 → p4)) → p5) → p3) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56675406211022312108673698896 : ((((p2 → p1) ∧ p4) ∧ ((p4 ∧ ((False ∨ (p1 ∧ (p2 ∨ p3))) → (p1 ∨ ((((p5 ∧ p3) ∧ p3) ∧ p2) ∨ (p3 ∧ False))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51179301036106912155824928934 : ((((((p3 ∧ True) → p5) ∨ (p1 ∧ (p1 ∨ (p1 → (False → (False ∧ p1)))))) → (p4 ∧ p3)) ∨ (((p4 ∨ p4) ∧ (True ∧ p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730386948395072902074849200633 : ((((True ∧ (p3 ∨ p2)) → ((((p4 ∧ p4) ∨ ((p5 ∧ False) ∨ (True ∨ False))) → p3) → ((((p4 ∨ p3) ∨ p5) → (p1 → p1)) → p3))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∧ p4) ∨ ((p5 ∧ False) ∨ (True ∨ False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111637231232204736518781186830 : ((((((p4 ∨ p1) ∨ ((((p3 → p1) ∧ p2) ∧ p4) ∨ False)) ∨ (p1 ∨ ((p1 ∧ ((True ∨ p4) ∧ p2)) → p1))) ∨ p1) ∨ False) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670795444981595722622410819459 : ((((p1 ∧ (((False → (p3 → (p1 ∨ ((True → (True ∨ (p5 → (p2 → (p2 ∨ p2))))) ∧ p3)))) ∨ p5) → False)) ∨ (p4 → (p1 ∨ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213161342328060655832694160634 : ((((p3 ∧ p2) ∨ p2) ∧ p4) ∨ ((p3 ∨ p2) ∨ (p1 ∨ (p4 ∨ (p5 ∨ ((p3 → (p4 → ((False → p4) ∧ False))) → (True ∨ (p4 ∨ p3)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260942217923429656319222558013 : ((p4 → False) → (p5 → ((p4 → (p4 ∧ ((((p2 ∧ ((p5 ∨ p1) → p5)) ∧ (False → False)) → ((p1 ∧ p4) ∧ (p4 ∨ p3))) ∧ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248614385823684686511910546732 : ((p3 ∨ False) ∨ (p5 → ((False ∧ ((False ∧ False) ∨ (p4 ∨ p4))) ∨ (((p1 → p2) ∨ (p4 → p5)) → (((p3 ∧ p4) ∨ True) ∨ (True ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_42727020782454305749733095528 : (((True → (((p5 → (((p2 → True) ∨ (p2 ∧ p4)) → ((False → (p1 ∨ p3)) ∧ (p2 ∧ p1)))) ∨ ((p3 → p3) ∧ True)) ∨ p1)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341960601719071886173494869109 : (p2 → (((((p4 → ((p5 → (False ∨ (p2 ∨ (p2 ∨ True)))) ∧ p1)) → ((p1 ∨ (p1 → p1)) ∨ p5)) → p5) ∧ True) ∨ ((p2 ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136669442550889721887740357548 : (((p2 ∨ (True ∨ True)) → (p3 → (p5 ∨ (((((p1 → ((False → p2) ∧ False)) ∧ False) ∨ p5) ∨ p3) ∨ (p5 → p5))))) ∨ ((p1 → True) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337371398533252691162504448277 : (p1 → (((p5 ∧ ((True ∧ True) → (p2 ∧ True))) ∧ (p1 → ((False → ((False ∧ p4) ∨ (False → (p4 ∨ p5)))) → p4))) ∨ ((p3 ∨ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69386076518554785258950845274 : ((p5 → (p2 → (((p4 → ((p2 ∧ ((p4 ∨ p5) ∧ p2)) ∧ False)) ∧ ((p2 ∧ (p1 ∧ (((p1 ∧ p5) ∨ p5) → p4))) ∧ True)) → False))) ∨ p4) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : ((p1 ∧ p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h14 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h15 := h4 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180558631538074950870688932221 : (((((False ∨ p4) → (p4 ∨ (p3 ∨ False))) ∧ True) → (p5 ∧ (False ∧ True))) → ((((p1 ∧ p5) → ((p3 ∧ p4) ∨ False)) ∨ p1) ∧ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ p4) → (p4 ∨ (p3 ∨ False))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((False ∨ p4) → (p4 ∨ (p3 ∨ False))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h9
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (((False ∨ p4) → (p4 ∨ (p3 ∨ False))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h17
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h16
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184705256254684381174343471610 : ((((False → (True ∧ True)) ∧ (p1 ∨ p2)) → ((p5 ∧ False) ∨ p4)) ∨ ((True ∧ True) ∨ ((p1 ∧ (True ∧ (p2 → (p4 ∧ True)))) → (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977216725283512313348245690186 : (((True ∧ ((((p3 ∨ False) → ((((p5 ∧ p2) ∨ p2) ∧ p4) → (p4 ∨ p4))) → p3) ∧ ((p4 ∨ (p3 → (p4 ∧ p1))) ∧ (p2 ∨ True)))) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : ((p3 ∨ False) → ((((p5 ∧ p2) ∨ p2) ∧ p4) → (p4 ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h22 =>
            -- False on the left can always be used.
            apply False.elim h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h13
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h27 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h28 := h11 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h31 : ((p3 ∨ False) → ((((p5 ∧ p2) ∨ p2) ∧ p4) → (p4 ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h39 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h40 =>
            -- False on the left can always be used.
            apply False.elim h40
        case inr h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h42 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h43 =>
            -- False on the left can always be used.
            apply False.elim h43
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h44 := h4 h31
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h45 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h44
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h46 := h11 h45
      -- We need to get the left conjuct of h46 based on <expert-advice>.
      let h47 := h46.left
      -- One of the premise coincides with the conclusion.
      exact h47
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135570085827633466555071355503 : ((((((False ∧ (p4 ∨ (p4 ∧ ((p5 → True) ∨ (p4 → True))))) ∨ p1) ∨ False) ∧ p3) ∨ (((True ∨ p4) → True) ∨ True)) ∨ (True → (p5 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778190793721086781985176631831 : (((p1 ∨ ((p2 ∧ p3) → (p5 ∨ ((((p5 ∧ ((False ∧ p2) → True)) ∧ (p2 → (((True → p5) → False) ∨ p2))) ∧ p4) → (p2 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



