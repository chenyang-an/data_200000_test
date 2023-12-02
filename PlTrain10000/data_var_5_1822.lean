variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198421953530306558800829633055 : ((p4 ∧ ((p4 → p1) ∧ (True ∧ (p2 → p2)))) ∨ ((((((p5 ∨ (p5 → (True → p5))) ∨ True) → (p5 → (False ∨ p1))) ∧ p5) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_460331235688169483655167480771 : ((((p5 ∧ (p3 ∨ (((p4 ∨ p2) ∨ ((((True ∨ p4) → (p3 ∧ p2)) ∨ False) ∧ p3)) ∨ p3))) → (((p2 ∧ False) ∨ (p5 ∨ p3)) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216068695619805533519042050612 : ((p5 ∨ (p1 → (False ∧ p2))) ∨ ((((((False ∧ p4) → p4) → True) ∨ ((p1 ∨ p3) ∧ False)) → (p4 ∨ p3)) ∨ ((False ∧ (False ∨ p4)) → p1))) := by
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
theorem thm_5_vars_217382663570533657845292916206 : (((p5 ∨ (p2 ∨ p4)) ∨ p5) → ((((False ∧ p2) ∧ True) ∨ (True ∨ (p1 → ((p5 → False) ∨ p5)))) ∨ (p3 → (((p1 ∨ False) ∧ False) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137743995166463753578811842038 : ((p2 ∨ ((((((False ∨ p1) → (((p3 ∧ p3) ∨ p1) → p3)) ∨ p1) ∧ (p2 ∧ (p2 ∨ p5))) ∧ (p1 ∧ p1)) ∧ p1)) ∨ (p5 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148506451225036497101499492408 : (((p4 ∨ (((p2 ∧ False) ∨ (((p3 → p1) ∧ p4) ∨ p4)) ∨ True)) ∨ (p1 → ((p5 ∧ p5) → (p2 → True)))) ∨ (p3 ∧ (False → (p5 ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637581261296471129763269823651 : (((((((p2 ∧ False) ∧ False) ∧ ((p1 → p4) ∨ (True ∨ p3))) ∨ ((p4 ∨ (((p3 → False) → (False ∨ False)) ∧ True)) ∨ (p4 → False))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191255542375711882914912249579 : (((p3 ∧ p2) ∧ (p2 → (p2 → (False ∧ (p2 → False))))) ∨ (p3 → ((((True → True) ∧ (p2 ∨ ((p2 ∧ p5) → p2))) ∨ (p3 ∨ p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766917750966916911136191984791 : (((p4 ∧ (True → ((((((True ∧ False) → p5) ∨ (p1 ∧ p4)) → (((False ∨ (False ∧ p4)) → p2) ∧ p4)) ∧ p2) → (p2 ∧ (p2 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751656924757717948984442905043 : (((True ∧ (p3 ∧ ((p5 ∨ False) ∨ ((False → ((p4 → (True ∨ (True ∨ p3))) ∧ ((p2 ∧ p3) → (p4 ∧ p3)))) → (p2 ∧ (p2 ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26895337202539673493201240308 : (((p2 ∨ p5) ∨ (((((p4 → ((True → (p1 → p2)) ∧ p1)) ∧ (p2 ∨ p1)) ∨ p1) → p3) ∨ (False → (((p4 ∧ p5) ∨ p1) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218024056581994843371806161922 : (((False ∨ p3) ∧ (p5 → p3)) → (False ∨ ((((p3 ∨ p4) ∨ p1) ∨ False) → (((p5 ∨ True) ∧ (((p5 → p4) ∨ True) ∨ p1)) ∨ (p2 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184563587195492341136393718791 : ((((p5 ∨ (p2 → True)) ∧ ((p1 → True) ∧ p3)) → (False ∧ True)) ∨ (p4 → ((((p2 ∨ False) ∨ p4) → (((p3 ∧ p5) ∨ True) ∧ p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116018493902907602998382603471 : ((((p3 → p4) → (False → p1)) → ((((p2 → (p3 ∧ (True ∧ False))) ∧ p3) ∨ True) → ((((False → False) ∨ p5) → p2) ∧ p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680874964653657669108691507820 : (((((False → (True → False)) → ((p4 ∨ True) ∧ ((p2 ∨ (((True → True) ∧ p4) ∧ p3)) ∧ (True ∨ True)))) → ((True ∧ (p5 ∧ p5)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234835636242427924599223797837 : ((p5 → (p3 ∨ p1)) → ((p2 ∨ (p4 ∧ (p1 ∨ ((p3 ∧ p4) ∧ p5)))) ∨ ((False → ((p5 ∧ False) → (True → False))) ∨ ((p4 ∧ p1) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355402655525615911059991112946 : (p5 → ((p5 → ((True ∧ (p1 ∧ (((p4 ∨ ((p1 ∧ p4) → p1)) → False) ∨ ((p2 → ((p2 → p3) ∨ p5)) ∧ (True ∧ False))))) ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181388218192109445794719866983 : ((p1 ∨ ((p2 → p5) ∨ ((((p2 ∨ False) → (False → p3)) → p1) → p2))) → (p5 → (p4 ∨ (((True ∨ (p4 ∨ (False ∨ p2))) ∧ p4) ∨ p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111402763335458739770584532119 : (((p2 ∨ ((((((True → False) ∧ False) ∧ (True ∨ p4)) ∧ p5) ∨ ((((p3 ∨ p5) ∨ p3) ∧ (True ∧ p3)) ∨ p5)) ∨ p1)) ∧ p4) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264336935798349624342268317423 : (True ∧ (((True ∨ (True ∧ p2)) ∨ False) ∧ (True → ((((p1 → True) ∨ p3) → ((((p1 → (True ∨ p1)) → p1) → p2) ∨ p4)) ∨ (True ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60200719197058320897002158417 : (((p5 ∨ p5) → ((((False ∨ ((((p5 ∧ p3) ∨ False) → (p4 ∧ p3)) → ((p1 ∧ p3) ∨ (p2 ∧ False)))) ∧ p4) ∨ True) → (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357074120825622587957789612196 : (p5 → (((p5 ∧ True) ∨ p2) → ((((p2 ∧ p4) ∧ (p4 ∨ (p4 → p3))) ∨ True) ∨ (((False ∨ (p1 ∨ (p5 ∨ False))) ∨ p5) ∧ (p3 ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177961050171030825297059985639 : ((((p2 ∨ p1) ∨ (((p3 ∧ (p2 ∨ (False ∨ p3))) ∧ p5) → False)) ∨ False) ∨ (True ∨ ((p2 ∧ (False → p2)) → (p4 ∨ (p4 → (False ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65829390520251782789292117302 : ((p4 ∨ (((p2 → (p5 → p5)) → False) ∨ (True ∨ ((p2 ∧ (((p2 ∧ ((True → p5) ∨ p2)) → p2) ∨ ((p4 ∧ p3) ∨ p3))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243905008126467022505647978186 : ((True ∧ False) ∨ ((p2 → (False ∨ ((True ∨ (True ∨ (p1 → ((p2 ∨ False) ∨ False)))) ∧ (p4 ∧ False)))) ∨ ((p4 ∨ ((p2 ∨ p5) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208553068775058423108975081870 : (((p3 ∨ True) → (p5 ∧ (p2 ∧ p1))) → (((p1 ∧ p1) ∨ ((((p1 ∧ p4) ∨ p4) ∨ p5) → ((p1 ∨ (False → (True ∨ p3))) ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
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
theorem thm_5_vars_263133044990227372740061576531 : (True ∧ (((((p4 ∨ False) → p1) ∨ False) ∨ ((((p5 → (p4 ∨ p2)) ∨ (p3 ∨ (p3 → p2))) → p2) ∨ (p5 ∨ (False → p4)))) ∨ (True ∧ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118381386718679823863789935819 : ((p2 ∨ ((((p1 ∨ True) → False) ∧ (((p2 → False) ∧ (p4 → p2)) ∧ p4)) → (p1 ∧ ((((False ∧ p1) → p5) ∨ p2) → p1)))) ∨ (p4 ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h18 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h19 := h12 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h27 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h28 := h25 h27
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177751052187068718525012303707 : ((((True → p5) ∧ ((p2 ∧ (p5 ∧ (False ∨ p4))) ∧ (p1 ∧ p1))) ∧ p4) ∨ (p3 → ((p1 ∧ (p2 ∨ (((p1 ∧ False) ∧ p3) ∧ p4))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137651876865816313107100660910 : ((False ∨ ((p1 → (p4 ∧ False)) → (True ∧ (((((False → p4) ∨ True) ∧ p2) → ((p3 ∧ (p2 → p5)) ∨ p1)) ∧ True)))) ∨ ((False ∧ p3) → p4)) := by
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
theorem thm_5_vars_185814838952061110855006369084 : ((p5 → (p4 → ((((p4 ∧ p2) ∨ p1) → (p4 ∧ p5)) → False))) ∨ (p4 ∨ (p2 → (p3 → ((p2 ∨ (p1 ∧ (True ∨ False))) ∨ (True ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330239450565605486728837680224 : (True → (False ∨ ((((p5 ∧ p5) ∨ (p3 ∧ ((((p4 → ((p2 ∧ ((p5 ∨ (p1 ∧ False)) ∧ False)) ∨ p4)) → p5) ∧ True) ∨ p5))) ∧ p3) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : (p4 → ((p2 ∧ ((p5 ∨ (p1 ∧ False)) ∧ False)) ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h14
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118380062146037566761189580991 : ((p2 ∨ ((((p4 ∧ ((True ∧ p1) ∨ p4)) ∨ ((p2 ∧ p1) ∧ False)) ∨ False) ∨ (p3 → (((p1 → (p4 ∧ p5)) ∧ False) ∧ True)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611256222773498263908259744466 : ((((((p4 → p3) ∧ (((True → (p5 ∨ (False ∨ (((p4 ∨ (False ∨ p2)) ∧ (p4 ∨ (p2 → p1))) ∨ p5)))) ∧ p2) → p2)) → p1) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151587702494346789343826503119 : (((((p5 → ((p3 → p3) → p2)) → p4) ∧ ((p5 → p3) ∨ (((p2 ∧ p5) → p1) ∨ False))) → (True → p3)) → (((p1 ∨ False) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675865142874495239299201651405 : (((((p4 → (p4 ∧ ((True ∨ (p3 ∨ p5)) ∧ (p5 ∧ (p1 ∨ p5))))) ∨ (((p3 ∧ p3) → p2) ∧ True)) ∧ (((p4 ∨ False) → p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355932265372128648827018445602 : (p5 → ((((p2 ∧ p5) ∨ (True ∧ p1)) ∨ ((p5 ∧ p1) → (((((p3 → True) ∨ True) ∧ True) → (p3 → p5)) ∨ p2))) → ((p2 → p1) ∨ p5))) := by
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
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168405014105692356113798513613 : (((False ∧ True) → ((p1 ∨ (p3 ∧ p2)) → (((p2 ∨ (p3 ∧ p2)) ∧ p1) ∧ (p3 → p5)))) → ((p4 ∧ p5) ∨ (((p5 → True) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56117247519174584616136597397 : ((((p5 ∧ p5) ∨ (p4 ∨ p4)) ∨ (((((p3 ∧ (True ∨ p3)) ∨ ((p1 ∨ False) ∧ False)) ∨ p1) → ((p3 ∨ False) ∧ (p1 → p2))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152537440060386149057180372957 : ((((p5 → p1) ∧ True) → ((((p1 ∨ (p1 ∧ (True ∨ True))) → ((True ∧ p3) ∨ (False → p5))) ∧ p2) → p5)) → (((p1 ∨ p5) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46354158077827309593526310003 : (((((p1 ∨ True) ∨ (p5 → (p4 → (((p4 → p1) → (True ∨ p3)) → p3)))) → (((p3 ∧ (False → True)) → True) → p1)) ∧ (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328471030437937045962163730618 : (True → ((True → ((True ∨ ((p5 → ((p2 ∧ p4) ∧ ((p1 ∧ p2) ∧ p1))) ∧ (p3 ∨ p4))) ∨ p1)) → ((p1 ∨ p2) ∨ ((False → p3) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48081400258922065315821430372 : (((((True ∨ p4) → (p4 → (p5 ∨ False))) ∨ (((p5 ∨ (p4 → p4)) ∧ p2) ∧ ((((p2 → p5) → p2) ∧ p1) ∨ False))) → (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618315666568006092994088325111 : ((((((p2 → p1) → (p5 ∧ p2)) ∨ ((p1 ∨ False) ∧ (((p4 ∨ True) → ((p3 → (False → p4)) → (p4 ∨ p4))) ∧ (p1 → p1)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_758615604556660900494569747462 : (((p2 ∧ ((((p5 → p2) ∨ (True → ((p3 ∨ ((p5 → (p5 ∨ p5)) ∧ (((p3 ∧ p3) ∨ p5) → p2))) → p5))) ∨ (p5 ∨ p2)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665851314950360557512780695367 : (((((((p2 → (True → ((((((p2 ∨ p4) ∨ True) ∨ p3) ∨ p3) ∧ p1) → p3))) → True) → (p5 ∨ True)) → False) ∧ (p5 ∨ (p1 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165751099114497923199879472836 : (((p1 ∧ ((p3 ∧ True) → p4)) ∨ ((True → p3) ∧ (((p1 ∧ p3) → (p4 → p2)) → p1))) ∨ (True ∧ (p1 → (p1 ∨ ((True → p5) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342670427246483278702410202855 : (p2 → ((p1 ∧ (((p1 ∨ p3) ∧ True) ∨ ((p2 → True) → p3))) ∨ ((((p5 ∧ True) → False) ∨ ((p3 ∨ p2) ∨ True)) ∨ ((p5 ∧ p3) → p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112307410932467589949486698546 : (((p2 → (((p3 ∧ (p1 ∨ (((((p5 ∧ p5) ∧ p5) → True) ∧ ((p1 ∨ p4) → p2)) ∧ p4))) → (True ∨ p2)) → p4)) ∨ p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751229188404285125903548475323 : (((True ∧ ((p1 ∨ (p2 ∨ p4)) → ((False ∧ p1) ∧ (p3 ∧ (p5 ∨ (((p3 → (True ∨ False)) → (p3 ∧ ((p5 → p1) → p4))) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230217760827369250109612708305 : (((True ∨ p1) ∧ True) → (True → (((p1 ∧ p3) ∨ p4) ∨ (p4 ∨ ((False → (False ∧ p5)) ∨ ((p2 ∧ (p2 → False)) ∧ ((p5 ∨ p1) ∧ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319297923359489520440247730331 : (p4 ∨ ((((p5 → ((True → (p5 ∨ p3)) → (p3 ∨ p2))) ∨ ((True ∨ True) ∨ p4)) ∨ True) → (((p1 ∨ (True ∨ False)) ∨ p2) ∨ (p4 ∨ False)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
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
        case inr h7 =>
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
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317626559866347053743404640391 : (p4 ∨ ((((p2 ∧ (True → ((True → p1) → (True ∧ (p5 ∨ ((((True → p4) ∧ p4) → (p1 → p4)) → p3)))))) → (False ∨ p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305338610557844383801485376606 : (p1 ∨ ((((p3 ∧ (p1 ∧ p4)) → (p3 ∨ (p4 ∨ (p4 ∨ p4)))) ∨ (p4 ∧ ((p3 ∧ True) ∨ False))) → (p3 → (((p2 ∨ p4) ∨ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178542521431425166402319769221 : (((p4 ∨ ((((True ∧ True) ∨ True) → True) ∧ True)) → ((p3 ∨ p5) ∧ True)) ∨ ((True ∨ (((p3 → (p5 ∧ p5)) ∨ True) ∧ p1)) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57085165155552741202070125420 : ((((p1 ∧ p5) ∧ p2) ∨ ((p2 ∧ (p5 ∧ (p1 ∨ (True → False)))) ∨ ((p4 → ((p3 ∧ (False → p1)) ∧ (p1 → (True ∨ p1)))) → True))) ∨ p5) := by
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
theorem thm_5_vars_157043932170908379011461224798 : (((False ∧ (((False ∨ ((p1 ∨ p3) ∧ (p5 → False))) ∨ (True ∧ (p1 ∧ p1))) → (p4 ∧ p2))) ∨ True) ∨ (((p3 ∨ True) → (p4 → True)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317707365213631090368482881272 : (p4 ∨ ((((((p3 ∨ p5) ∧ False) ∧ (False ∧ (((p2 ∨ p3) ∧ p3) ∨ True))) ∧ (p1 ∧ ((p1 → p1) ∨ (p1 ∧ p5)))) ∨ (p1 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741400725494698564373175351191 : ((((p5 ∨ False) ∨ (True ∧ (((False ∨ ((True ∨ (p1 → ((p1 ∧ p5) ∧ p1))) → (False ∨ p5))) ∧ (((False ∧ p2) ∨ p3) ∨ p1)) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219373954541954949422336416841 : ((p3 ∨ ((p3 ∧ True) → p1)) → (((((p4 ∧ p1) → p4) → ((p4 ∧ p1) ∧ (p1 ∧ p5))) ∨ True) ∨ (p3 ∧ (p3 ∨ ((p4 ∨ p1) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643981791227161096803755795875 : ((((True ∨ ((((((p5 ∧ (p3 ∨ p5)) ∨ p3) ∨ p2) → ((True → True) ∨ p3)) → (((p2 ∧ (p4 → p1)) ∨ p3) ∧ p3)) → p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36260718753600773155355712486 : ((p4 → (((False ∨ p3) ∧ ((p2 ∧ (p5 ∧ (((p2 ∧ ((p3 ∧ p4) ∧ (((p1 → p3) ∨ p3) ∧ False))) ∨ p4) ∧ p2))) ∨ p1)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153534466784950804038395415309 : ((True → ((((((p5 → p5) → p4) ∧ ((False ∨ p2) → (p3 → True))) ∨ False) ∧ False) ∧ ((p4 ∨ p3) ∧ p1))) → ((p4 ∨ p2) → (True → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173448843411961934737072357596 : (((((p5 ∨ False) → (((p4 → p5) → (p2 ∨ (p5 ∧ True))) → p2)) ∧ p4) ∧ p5) → ((False ∨ (p1 ∧ ((p4 ∨ False) → p1))) ∨ (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262478436030285028586473526379 : (True ∧ ((p5 ∨ (((((True ∧ False) ∧ (p1 → (((p2 ∨ (False → True)) ∧ True) ∨ (p3 ∧ (False → False))))) ∨ True) ∧ p5) ∧ (p3 ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166411943111722508796101184947 : ((p1 ∨ ((p1 → ((((p1 ∨ p3) ∨ True) → (p2 ∨ p4)) → ((p4 → p5) ∨ p4))) ∨ True)) ∨ ((((p1 → p2) ∧ (p1 → p5)) → p3) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200369343527974780004026913746 : (((p3 → True) ∧ (((p3 ∨ p3) ∨ p2) ∨ p1)) → (((p2 ∨ (p5 ∧ (p2 → ((p3 ∧ (p1 → (p3 ∧ True))) ∨ p1)))) ∧ (p1 ∨ p2)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
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
theorem thm_5_vars_168083640936738108736628486007 : (((p2 → ((p4 ∨ p5) ∧ False)) ∧ ((((p3 ∨ False) → p3) ∨ p2) ∧ ((True → p4) → p1))) → ((p2 ∧ (p5 ∧ True)) → ((p1 ∨ p2) → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h25 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h26 := h20 h25
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h29 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h30 := h20 h29
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113846646209203487314613420661 : (((p5 ∨ (((True ∨ ((p1 → p2) → (True → True))) ∨ p4) → (p1 → ((((p2 → p1) ∨ True) ∧ True) ∨ False)))) → (p1 → p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308383333707707986983775171316 : (p2 ∨ ((((p4 → ((p2 ∧ ((p1 → (False ∧ (((p1 ∧ False) → p5) ∧ p4))) → p1)) ∧ True)) ∨ (p1 ∧ ((p5 ∧ True) → p3))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323659692478351071486145363092 : (p5 ∨ ((((p5 → (p3 ∧ ((p5 ∧ p1) ∨ (p1 → ((p4 → p1) → False))))) ∧ (p3 → False)) ∧ (p5 ∨ p3)) ∨ (((p2 → True) → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793230543708126968558314799221 : (((True → (p1 ∧ ((((p5 ∧ (p4 ∧ (True → p5))) → (p5 ∧ p2)) ∨ (p4 ∧ p1)) ∨ ((p3 ∨ ((p4 ∨ p1) → False)) ∧ (p2 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105507561429459904609917612444 : (((p1 ∨ (p1 ∧ (p3 ∧ ((((((p5 ∨ p4) → True) ∧ (p4 ∧ p2)) → p5) → False) ∧ True)))) ∨ (p4 → (True ∨ (p2 ∨ p3)))) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171628509375486534545134089929 : ((((p5 ∧ (True ∨ True)) → ((((p4 ∧ p2) ∧ (p5 ∧ True)) ∧ False) ∨ True)) ∨ p5) ∨ (False ∨ ((p2 ∨ ((False → (p1 ∧ p3)) → p1)) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197887750827696861902963433840 : ((((p4 ∧ p1) → p1) → (p4 ∨ (p3 ∨ p1))) ∨ ((p2 ∨ p5) → ((p4 ∧ p5) → (p1 ∨ (((p5 ∨ False) ∨ (p3 ∧ p3)) ∧ (p5 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244373988034517463079786857581 : ((False ∧ p1) ∨ ((False ∨ ((False ∧ False) ∧ (p2 ∨ (((p4 → (((True ∧ (True → (p2 ∨ (p5 ∧ p5)))) ∨ True) → True)) → False) → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153576250214508277538113735520 : ((False → ((p2 ∧ ((p4 ∨ p2) → ((((p2 ∨ (p3 → (p5 ∨ p5))) ∧ p4) ∨ (p5 → p2)) ∨ p5))) → p3)) → ((True → False) → (p2 ∨ p5))) := by
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
theorem thm_5_vars_39070747220928060297508431548 : ((((False ∨ False) ∨ (((True ∧ ((((p2 → False) → ((p5 ∧ ((p5 → p5) → True)) ∧ p1)) ∨ p3) ∧ (False ∧ p1))) ∧ p1) ∨ True)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205710621096124870686117722046 : (((p1 → p4) ∨ (p3 ∧ (False ∧ p2))) ∨ ((p2 ∧ (False ∨ (p4 → p2))) ∨ (True ∨ (p4 ∧ (True ∧ ((p4 ∨ p2) ∧ (p4 → (False ∨ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2325666754192465242735817305 : ((p4 ∨ (p5 ∧ (((p5 ∧ p3) ∧ (p4 ∨ False)) → (p2 → (False ∧ p2))))) → ((True → (((p4 ∧ (True ∧ False)) ∨ p2) ∨ p3)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62945991161573414683133151814 : ((p4 ∧ (p4 ∧ (p2 → ((((((p1 ∨ True) ∧ False) ∨ (True ∨ True)) → (((p5 ∧ p5) ∨ (p5 ∨ p5)) ∧ p1)) ∨ (True ∨ p3)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703417645535918010287652546617 : ((((p3 ∨ (((p5 → ((p4 ∨ True) ∧ p2)) ∧ True) ∧ p3)) ∨ (p3 ∨ (p4 ∨ (((p2 ∨ False) → (p1 ∧ False)) ∨ ((p4 → p5) ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351919804283439733216507642138 : (p4 → ((p1 ∨ (p1 ∧ ((p3 ∧ p1) ∨ (p1 ∧ (p1 → p4))))) ∨ ((p4 ∨ (False ∨ (p4 ∧ False))) ∨ ((p3 ∨ p1) → (p5 ∧ (False ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171653030115760914878876234530 : (((False ∧ ((((p1 ∨ (p2 ∨ p5)) ∨ ((True → p2) ∧ True)) → p5) → p5)) ∨ False) ∨ (((p3 ∧ ((p5 ∧ True) ∧ (True ∧ p4))) → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245327422054699023290355546233 : ((p2 ∧ p2) ∨ (p3 ∨ ((((p1 → (p2 → False)) → ((p1 → p4) → (p4 → p4))) ∨ ((True ∨ (p3 ∨ p5)) ∨ (p4 ∧ (True → False)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_132860048931861511521861148038 : ((p3 ∨ ((False ∨ (((p5 → p3) → (((p4 ∨ (p2 → p1)) → False) → ((True → (p1 → p3)) ∨ True))) ∧ True)) ∨ False)) ∧ (True ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159061842767566709069857140792 : ((p5 ∨ (((p5 → False) ∧ p1) ∨ (p5 ∧ ((p3 ∧ (p5 ∧ p5)) → (((p5 ∨ p4) ∧ True) ∧ p1))))) ∨ (((p3 ∨ True) ∨ (True → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60343488056027790223548020250 : (((p2 → p2) → (True ∧ ((((p4 ∧ p5) → (((p1 ∧ p1) ∧ p2) ∨ (p5 ∧ (p2 ∧ (p3 ∨ True))))) ∨ p1) ∨ (True ∧ (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300774366618414629602180783806 : (False ∨ (((p4 ∧ ((p1 ∨ (p4 ∧ (p5 ∧ ((p1 ∨ (p4 ∨ p4)) ∨ p1)))) ∨ p3)) ∨ True) ∨ ((p1 → (p4 → (p3 ∧ p1))) → (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179063310879158136499141677890 : ((True ∧ ((p4 ∧ ((p3 ∧ (p2 → (p1 ∨ p4))) ∨ (p3 ∧ True))) ∨ p2)) ∨ (((p5 → (p3 ∨ p1)) → (False → (p5 → True))) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202425328010305185018591590097 : (((True ∨ (p2 → p2)) ∧ (p1 → p1)) ∧ (((((False ∨ (p3 ∨ True)) ∧ True) → (p2 ∨ (p1 → False))) ∧ p3) ∨ (True ∨ ((p5 → False) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247438651546858771366567675552 : ((False ∨ p2) ∨ (((True → p3) ∨ p2) → ((((True ∧ ((p3 → p1) ∧ p2)) ∧ (p3 → (p5 → (True ∨ (p4 ∨ p1))))) ∧ p1) ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156657136590957778890249515768 : ((((((p2 ∨ p5) ∧ p3) → (True ∧ (p2 ∨ ((False ∧ (p3 → p4)) → (True → True))))) → p1) ∧ True) ∨ (((False ∧ (p2 ∨ False)) ∧ p1) → p2)) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60475221089853193411588733366 : (((p5 → p5) → (((p1 ∧ (p3 → p5)) → ((((p2 ∨ True) ∨ p2) → p4) → ((p2 → p5) ∧ (p4 ∨ ((p4 ∧ p2) ∨ p1))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87417038412829498606534343643 : (((p1 ∨ ((False → p5) ∧ (p3 ∧ p4))) ∧ (p5 ∧ ((p3 ∨ (p5 ∧ p4)) → ((p5 ∧ p3) ∨ (False → (p4 → ((p1 → p5) ∨ p3))))))) → p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55128395811818846241234455577 : ((((p3 ∧ ((False ∨ True) → p2)) ∧ p1) ∨ ((p4 → (p1 ∨ (((p2 ∧ p3) ∧ (True → p1)) ∨ ((False ∨ p2) ∨ (False → p5))))) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_65410294166035068932286949060 : ((p3 ∨ ((True ∨ ((p3 ∨ p4) → p3)) → (((p1 ∧ ((False ∧ (((p3 → p4) → p2) → p3)) → True)) → p2) ∨ ((p1 → p1) → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_2366424900034462897769479052 : ((((False ∨ p3) → (p2 ∨ ((p2 → p3) ∨ (p4 → p4)))) → p3) ∨ (p1 → ((False → p1) → (False → (((True ∨ p4) → False) ∧ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656797168914980886288665122765 : ((((((p4 ∨ p3) ∨ (p3 → (p2 → p2))) → ((((((p5 → p5) ∧ True) ∧ p4) → p5) ∧ (True → p5)) ∧ (p4 → False))) ∨ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48068052175287958524454173563 : ((((False ∨ ((False ∧ (False → (p1 ∧ p3))) ∧ True)) → (((((p2 ∨ p2) ∧ ((p5 → p1) ∧ True)) → False) ∧ p4) ∧ p1)) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



