variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8368992303039620443878921612 : (((((p3 ∨ (p2 ∨ (p4 ∧ p3))) ∧ (((((p5 ∧ (False ∧ (True ∧ ((p5 ∧ p1) ∧ p4)))) → False) → p3) ∨ p5) → p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52529258585095908378177631370 : (((((p1 ∨ ((p3 → p2) ∧ (p5 ∧ p1))) ∧ (False → (p5 → p2))) ∨ False) ∨ ((p1 ∨ (p5 → (((p1 ∨ p5) ∨ p2) ∨ p4))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247411363475876904824242003251 : ((False ∨ p2) ∨ ((p5 → ((p1 ∨ (p4 ∨ (((p2 ∨ p4) ∨ True) ∧ p1))) → (((((False ∨ p5) ∧ (True ∨ p4)) ∨ p4) ∧ p3) ∨ True))) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124111577766442283242710820604 : ((((((p1 → (p5 → p1)) ∨ p5) ∨ p1) → (False ∧ p3)) ∧ (((p4 ∨ ((p4 ∧ (p1 → True)) ∨ p3)) ∨ (p4 → p3)) ∧ p3)) → (p1 → p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (((p1 → (p5 → p1)) ∨ p5) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h16 : (((p1 → (p5 → p1)) ∨ p5) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h17 := h3 h16
        -- We need to get the left conjuct of h17 based on <expert-advice>.
        let h18 := h17.left
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h20 : (((p1 → (p5 → p1)) ∨ p5) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h21 := h3 h20
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h24 : (((p1 → (p5 → p1)) ∨ p5) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h25 := h3 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178303697225827168154777127334 : ((((((p5 ∧ (False → True)) ∧ (p4 → p4)) → p4) ∧ False) ∨ (p3 ∨ p2)) ∨ (p1 → (True ∧ ((False ∨ p1) ∧ ((False ∨ p5) → (p5 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679722769972431580315024389033 : ((((((((False ∨ p3) → ((((p4 ∧ True) ∧ (p1 ∧ False)) ∧ p4) → p4)) → True) ∨ (p2 ∨ p1)) ∨ p2) → (p5 ∨ ((p4 → p1) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159225232873261866230079306098 : ((p2 → (p3 → ((((True ∧ p1) ∧ p4) ∧ (p3 → p1)) ∨ (p4 ∧ (False ∧ ((p5 ∨ False) ∧ False)))))) ∨ ((p3 ∧ ((p5 ∨ p3) → False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789608805382531929488120851151 : (((p5 ∨ ((((p4 ∧ ((p1 ∨ True) ∧ False)) ∧ p5) → p3) → (((False ∨ p1) ∧ p3) → (((False ∨ p1) ∧ (p2 → (p2 ∨ p1))) ∧ p3)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646058213641543907109778345067 : ((((True → (p2 ∧ (((p2 → (p1 ∨ p1)) → (p4 ∨ (p5 ∨ (True → False)))) ∧ (False ∧ ((True ∧ (False ∨ (p5 ∧ False))) ∧ False))))) → p1) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51888676528609961403087190221 : (((((((p4 ∨ p4) ∨ ((False ∧ p4) → p3)) ∧ p4) ∨ (p3 ∧ (p2 → True))) → p1) ∨ (p1 → (p5 ∧ ((False ∨ p1) → (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115404803280055529751960060090 : (((p3 ∨ ((p1 ∧ ((p4 ∨ p3) → p4)) ∧ p2)) ∧ (p2 ∨ ((p4 ∧ p2) ∨ ((p4 ∧ ((True ∨ True) ∨ (p5 → p1))) ∧ p1)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307891748467315547257750667205 : (p1 ∨ (p5 → (False ∨ ((((p4 ∧ (True ∧ (((False → p5) ∧ (p1 ∨ p3)) ∧ ((True ∨ (p2 ∧ p2)) ∨ (p3 ∨ False))))) ∨ p1) → p2) ∨ p5)))) := by
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
theorem thm_5_vars_786108911586975444231419594127 : (((p4 ∨ (((((True ∧ (p4 ∨ False)) ∧ (p2 → False)) ∧ (p4 ∧ (p1 → p4))) ∧ ((p5 ∨ (True → p5)) ∧ p5)) ∧ ((p1 ∧ p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135404565742215308053177183557 : (((((p3 ∨ p1) ∧ ((p5 ∨ p2) → p1)) ∨ (p3 ∧ (((False → (p5 ∨ p5)) ∨ p3) → p2))) ∨ (True → (False → True))) ∨ ((p5 ∧ False) ∨ False)) := by
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
theorem thm_5_vars_204643126553004018815923245266 : (((p1 ∧ (p3 → (True ∨ True))) ∨ p5) ∨ ((p5 ∨ p5) → ((((p5 ∨ (p4 ∧ p5)) → ((True ∧ False) ∧ p3)) ∧ False) ∨ (p3 → (False → False))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348005631659936180995602273887 : (p3 → ((False ∧ p1) ∨ (((True → False) ∧ ((p2 → (p3 ∨ p3)) → (p4 ∧ (True ∧ (p3 ∧ p4))))) → (((p1 → (p5 → False)) → p2) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322336403903280436479468046759 : (p5 ∨ (((p5 → (((((p2 → p1) ∨ p3) → (p2 ∧ p3)) ∧ p5) ∨ ((p4 ∨ p3) ∧ (p1 ∧ ((p3 ∧ p5) ∧ p3))))) ∨ (p1 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307677965222152002872383271600 : (p1 ∨ (p2 → ((((((((((p3 ∨ p1) ∧ (p4 ∧ False)) ∨ True) ∧ True) → (True → p2)) ∧ True) ∧ p4) ∧ (False ∨ p1)) → False) ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351828398517783016007657546606 : (p4 → ((p3 ∧ (((False ∧ (p4 ∧ (p1 → (p4 ∧ p3)))) ∨ p1) ∧ p3)) ∨ ((((p4 ∧ p1) → (p4 ∨ ((False ∨ p3) ∨ p4))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58137992051301154059461556372 : (((p2 ∧ p2) ∧ ((((p2 → (((False ∨ p2) ∨ p1) → p2)) ∨ p1) → p3) → ((((p2 ∨ p1) → True) → (p5 → p4)) → (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694601821348304352177371424328 : ((((p4 ∧ ((((p3 ∨ p1) → (p4 ∨ p2)) ∨ p3) ∧ (False → (p5 ∧ p5)))) ∨ (p1 ∧ (((True ∧ p2) ∨ (True ∧ p3)) ∧ (p5 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230618182071643878134383202610 : (((p2 → p2) ∧ p1) → ((((p2 ∧ p1) → p3) → ((((((p1 ∧ (p2 → p1)) → p2) ∧ p5) ∧ p5) ∨ False) ∨ p4)) ∨ ((p5 ∧ p4) ∨ True))) := by
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
theorem thm_5_vars_354765576495369089186526578282 : (p5 → ((((p1 → (((False ∧ p1) ∧ p5) ∨ p2)) ∨ ((p1 ∧ p3) ∧ p1)) ∨ (((p4 ∧ p4) ∧ False) → ((p5 ∨ (p5 → p3)) ∧ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171387340643297898131268445586 : (((((p1 ∨ (p5 ∨ (False ∨ p1))) ∧ p2) ∧ ((True ∨ (p1 ∧ False)) ∧ p2)) ∧ p1) ∨ (p4 → (((p5 → False) ∨ p4) ∨ (False ∧ (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595422456588013232499927884180 : (((((((p2 ∨ (p4 ∧ ((p5 ∧ (p2 ∧ p2)) → True))) ∧ p3) ∨ p4) ∨ ((True ∨ (((p3 ∧ (p4 ∧ False)) → p3) ∧ False)) → True)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42531991168547297311373611635 : (((p1 ∨ ((p3 ∨ (p5 → (((p3 → p4) → True) → (p1 ∧ (p3 ∧ ((((True ∧ True) → (p2 ∨ True)) ∨ False) → p2)))))) ∨ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197309882824103683037212518137 : ((((p3 → p1) ∧ ((p1 ∨ p1) ∨ p1)) → False) ∨ ((True ∨ (p3 ∨ p5)) ∧ (p4 → ((((True ∧ (p1 ∨ p2)) ∨ True) → p4) ∨ (p5 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197135961705678738230622032081 : (((p5 ∨ (False ∨ ((False ∧ p1) ∨ p1))) ∨ True) ∨ (((p5 ∨ (True ∨ (p2 ∧ (p3 ∨ (True → (False → p3)))))) → (p5 ∧ (False ∧ p4))) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118400045703852720257807328972 : ((p2 ∨ ((False ∧ p1) ∧ ((p4 ∨ (p1 ∧ (p5 ∨ (((True ∧ ((p5 → p4) ∨ (False → True))) ∨ True) → p2)))) → (False ∨ True)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219891599106999679317024170905 : ((p4 → ((p2 ∧ p1) ∨ p3)) → (((p5 ∧ ((p2 ∨ (((p4 ∨ (p1 → False)) → p5) ∧ (p3 → ((True ∧ p2) ∨ p2)))) ∨ p5)) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192495140587022047453665718685 : (((((p5 ∧ p4) → p3) → ((p2 → p3) ∨ p5)) ∨ p3) → (p2 ∨ (True ∧ ((True ∧ ((p2 ∨ p5) ∧ p1)) → (p1 → ((p4 ∧ True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159581224411021908119462377596 : (((False → (True ∧ ((True → (p1 → p4)) ∨ ((p3 ∨ (False → True)) ∧ ((p3 → p2) ∧ p5))))) ∧ True) → ((True ∧ p4) ∨ ((p2 ∧ p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201248482667885747217203048284 : ((p3 → (((True ∧ p1) ∧ (p4 ∨ True)) ∨ False)) → ((p3 ∨ (True → (False ∧ (((p4 ∨ p2) → False) ∨ (p2 → (p1 → p3)))))) → (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674728198902921250017617363033 : ((((p3 → ((p1 → ((((p2 → p4) ∨ p5) ∨ ((p1 ∧ (p2 ∧ p3)) ∨ (False ∧ (p3 ∨ p3)))) ∧ p5)) ∧ p1)) → ((p4 ∨ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170990153389442372590715962117 : ((p2 ∨ (p1 → (((False ∧ (((p5 ∧ (p5 ∧ False)) ∧ p1) → p1)) ∧ p1) ∨ p1))) ∧ (((p1 ∧ (p1 ∧ p1)) ∨ (True ∨ (p4 ∨ p5))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305798036635096130794052044217 : (p1 ∨ ((((False → (False ∨ p2)) ∧ (p2 ∧ p1)) → False) → (p2 → ((((((p2 ∨ p1) ∧ (p3 ∧ p4)) → True) → p3) ∨ (p2 ∨ p4)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72126002680567455409661973749 : (((True → ((p1 ∨ ((p5 ∨ (True ∧ (True → (p5 → p3)))) ∧ (False ∨ False))) ∧ ((p2 ∧ ((True ∨ (p4 ∧ p3)) ∧ p4)) ∧ False))) ∧ p2) → p3) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717502458896228205790493634913 : ((((p2 → ((p4 ∨ False) ∨ False)) ∧ ((p4 ∨ p5) ∧ (p5 → ((p3 ∨ (((p4 ∧ (p2 ∧ (p4 ∧ False))) → (p5 → p3)) → p3)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104584458599225854503173392850 : ((((p5 ∧ ((p1 → p1) → (((True → p5) → p4) ∨ (p5 ∨ p2)))) ∧ (p4 ∨ (p1 ∧ ((p4 ∨ False) ∨ p5)))) ∨ (p2 → True)) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65289986421338323684119251709 : ((p3 ∨ ((((p5 → (((p1 ∨ p2) ∧ p3) ∧ p4)) ∧ ((p1 ∨ (p2 ∧ p3)) ∨ p4)) ∨ ((p3 ∧ (p5 → p4)) → True)) ∨ (p1 → False))) ∨ p5) := by
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
theorem thm_5_vars_214303992368365677815491695030 : (((True ∨ (p2 ∧ p4)) → False) ∨ ((True ∧ p3) → (p2 ∨ (((p2 ∧ (((p1 ∧ False) → p5) → ((p4 ∨ p1) ∧ p1))) → (p1 ∨ p4)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∧ False) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h7
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345655061647438171059422436109 : (p3 → ((p5 ∧ (((p1 → (p5 ∧ (p2 ∧ (False ∨ ((p5 ∧ False) ∧ p4))))) → p5) → (p2 ∨ (False ∧ ((p5 ∨ (p1 ∨ p4)) → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336116612162010640018435425540 : (p1 → (((((p2 → p1) → (False ∨ (p3 ∧ ((True ∧ p3) → ((p5 → (True ∨ (False ∨ p3))) → (p3 ∧ p3)))))) ∧ (p5 ∨ True)) ∨ p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206758793792023504557781385552 : ((p4 → ((p1 ∧ (p3 ∨ p3)) ∧ False)) ∨ (((p4 ∨ p2) ∨ (((False → (((p3 ∨ (p5 → p1)) ∧ p4) → p4)) ∨ (p3 ∨ p2)) → True)) ∨ p1)) := by
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
theorem thm_5_vars_166745039362471892658301063683 : ((p4 → ((((p3 ∨ p3) ∧ ((p3 → p4) ∧ p2)) ∧ p1) ∨ (((p5 → p3) ∨ p2) ∨ True))) ∨ (((False ∧ True) ∨ ((False ∧ True) → p2)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428603922947299083533464213032 : (((((True → ((p5 ∨ (p1 ∨ (((p3 ∧ True) ∨ (p2 ∨ (((p3 ∨ p3) ∧ p2) ∨ p1))) ∧ (p5 → p5)))) → p1)) → p2) ∨ (p5 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123152597448053252246455248674 : (((True ∧ (((p4 ∨ (p2 ∨ p4)) ∧ (True → (((False → False) ∧ ((p4 ∨ False) ∧ p3)) ∧ p5))) ∨ p4)) → ((p1 ∨ p4) ∨ p5)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168718664006466959158937253846 : ((True ∨ (True ∧ (((((p3 ∧ p1) ∨ p4) ∨ p5) ∨ (True ∨ (p5 ∧ p1))) ∨ (p1 ∧ p3)))) → ((((p1 ∨ False) → (p3 ∨ p4)) → p3) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753347313245716786272458905661 : (((False ∧ ((p3 ∨ ((True ∨ ((p4 → (True → (True ∨ p4))) → (False ∨ p4))) ∨ ((False → p5) ∧ (p4 ∨ (p1 → p3))))) → (p1 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178710251292329800981161390238 : (((p5 ∨ ((p1 ∨ p3) ∧ p2)) ∨ (False ∧ ((True ∧ False) → (p5 ∨ p3)))) ∨ ((((False ∧ True) ∧ False) ∧ (p5 ∨ (True ∨ (p2 → p4)))) → p1)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198196738705486861117584862946 : (((p1 → p5) → (p3 ∧ ((p2 → p3) ∧ True))) ∨ (((p2 ∨ False) ∨ p4) → (((False → (p1 ∨ p3)) → True) → (False ∨ ((False ∧ p3) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683935695622219771111626614362 : (((((((False ∧ (p4 → p2)) → ((((False ∧ True) ∨ (p4 ∧ False)) → p1) ∧ True)) ∨ p4) → p5) ∨ (((False → p5) ∨ (p4 ∨ p4)) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118818827891792681750125830760 : ((True → ((((p2 ∧ (p2 → (False ∨ (((((p4 ∧ False) → (p1 ∨ True)) ∨ (p5 ∧ p2)) → p3) → p4)))) → p5) ∧ p1) → p4)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250940918925970160457730013715 : ((p1 → p4) ∨ ((((((p5 → ((True ∧ p4) ∧ (False ∧ (p5 → (True → p5))))) ∧ (p1 ∧ (p3 ∧ p3))) ∧ p3) ∧ False) ∧ p3) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719158426359817202289432669061 : ((((p1 ∧ (p2 ∨ (True ∧ p4))) ∨ ((((p1 ∨ (p3 ∧ (p3 → p4))) ∧ (p2 ∧ p3)) → ((((p4 ∨ p1) → p4) ∨ p1) ∨ p3)) ∨ p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165545264668215970303877170048 : (((((p1 ∨ p3) → (p5 → p1)) ∧ (True ∧ p5)) ∧ ((p1 → p3) → (p4 ∨ (p4 ∧ True)))) ∨ (((True ∧ (p2 → p4)) → p2) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180020188156089770731462115661 : (((True ∧ ((((p3 ∨ p2) → True) → False) ∧ (p4 → (True ∧ p5)))) ∨ False) → (True → ((p2 ∨ (True ∨ (p1 ∨ (p5 → (p5 → p5))))) → p2))) := by
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
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h18 : ((p3 ∨ p2) → True) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h20 := h16 h18
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h29 : ((p3 ∨ p2) → True) := by
            -- Implications on the right can always be decomposed.
            intro h30
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h31 := h27 h29
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h36.left
          let h38 := h36.right
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h39 : ((p3 ∨ p2) → True) := by
            -- Implications on the right can always be decomposed.
            intro h40
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h41 := h37 h39
          -- False on the left can always be used.
          apply False.elim h41
        case inr h42 =>
          -- False on the left can always be used.
          apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143151113492686071706731795268 : ((p1 → (p4 ∧ (p5 ∧ (True ∧ (p1 ∧ (((((p4 ∨ p4) → ((p2 → p5) ∧ (True ∧ False))) ∧ False) ∨ p5) → p2)))))) → ((False ∨ p4) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778713514230030704043291748441 : (((p1 ∨ (p3 ∨ ((p4 → p1) ∧ ((((True ∧ ((p3 ∨ p5) → False)) ∨ (p4 → False)) → True) ∧ (((p4 ∨ (p4 → False)) ∨ p4) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763631244486514002454287793956 : (((p3 ∧ (p5 ∧ ((True → ((((p1 ∧ p1) ∧ p1) → (p5 ∧ p4)) ∧ p3)) ∧ (((p1 ∧ (False ∧ False)) → ((p3 → p4) ∧ p2)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51731848098538127574765389544 : ((((p3 ∨ (True ∧ (p1 ∨ False))) ∨ ((False ∧ (p4 ∧ (p4 → (p4 → p5)))) → p4)) ∧ (((((p4 ∧ p3) ∨ True) ∨ p4) ∨ p2) ∨ p3)) ∨ p4) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133472060375460858021980433687 : ((p5 → ((((False ∨ (p1 ∧ p3)) ∧ (p1 → False)) ∧ (((p4 → p5) ∨ p2) ∧ p1)) ∨ ((p5 ∨ True) ∨ (p5 ∨ p4)))) ∧ (False → (p5 ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355568643100254122836768360197 : (p5 → (((((((p5 ∨ False) → (False ∨ p3)) ∨ (False → p5)) → ((p4 → (p2 ∧ p4)) ∨ p4)) ∨ False) ∧ ((p1 ∨ False) ∧ p3)) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204188005532666559449974804022 : ((((p5 → (p4 ∧ p2)) ∨ p2) ∧ False) ∨ ((p2 ∨ ((((False → (False → True)) ∧ True) ∧ p2) ∨ p5)) → (((p5 ∨ p1) ∨ p4) ∨ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150169845850496637098652844097 : ((p1 → ((False ∧ p1) ∨ (((((p3 → ((((False ∨ False) → p4) → p3) ∧ p1)) → p4) ∨ p4) → p2) ∨ p1))) ∨ ((p5 ∧ (p1 → p2)) ∧ True)) := by
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
theorem thm_5_vars_152810822113111449412686527602 : (((p1 ∨ False) → ((p2 → p1) ∨ ((p5 → True) ∨ (((p3 ∧ p3) → ((p5 ∨ p5) ∧ p5)) → (False → p4))))) → (((p4 ∨ True) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60048080491409720441316282705 : (((p2 ∨ True) → (((((True ∧ p3) → (p5 → (False → (p4 ∨ ((p4 → p1) ∧ p4))))) → ((p3 → (p3 ∧ p5)) ∨ p4)) ∧ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191247050593787425323732802731 : (((p1 ∧ False) ∧ (((True → p4) ∨ p1) → (False ∨ p3))) ∨ (((p3 ∧ p4) → (p4 ∨ False)) ∧ (((((p2 ∨ p2) → p3) ∨ p4) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689262144481084152522920045355 : (((((True → (True → ((False → (p3 → (p1 ∨ (p5 ∧ p3)))) ∧ (p2 ∨ True)))) → p2) ∨ (((p4 ∧ False) → p1) ∨ (p4 → (True → p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227049366503811112249943769691 : (((p2 ∨ p4) → p3) ∨ ((p1 ∨ True) → (p2 ∨ (((((True → p1) → (p5 ∨ (p4 → p2))) ∨ (p5 ∨ True)) ∨ (p5 ∧ (True → p4))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655626588058483013528961915944 : (((((True → ((p2 ∧ (p5 → (p4 ∧ p4))) ∨ ((p2 ∧ (((p3 ∨ p4) ∨ p4) ∧ False)) ∨ (p5 ∨ p1)))) → (p1 ∧ False)) ∨ (True ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_663987713381298825926667293418 : ((((p5 ∧ (((((p5 ∨ p1) ∧ p4) ∧ ((p5 ∨ p3) ∧ (p3 → True))) ∧ (p3 ∧ (p4 ∨ (p5 ∧ (p2 ∨ p3))))) ∨ False)) → (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117341019352033235029895066527 : ((False ∧ ((p4 ∧ p3) ∨ (((((p2 → (p3 ∨ p3)) ∧ p5) ∧ ((True ∧ (p3 → (p2 → (False ∨ False)))) ∧ False)) → p2) ∧ p4))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49637257508437939269921185159 : (((((p1 → (True ∨ p3)) ∨ p1) ∧ (((p3 → p3) ∨ p1) ∧ (((p4 → False) ∧ (p1 ∧ True)) ∨ (p2 ∧ True)))) → ((p2 ∨ p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352459914055926221068332719868 : (p4 → (((False ∧ p5) → p1) → (p5 ∨ (((p3 ∨ (p5 → (p2 ∧ p1))) ∨ ((p1 ∨ ((p4 ∧ p2) ∨ p4)) ∨ (p1 → p1))) ∨ (p2 → p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186567153646560447760953938571 : (((p1 ∨ ((p2 → (p3 ∧ p1)) → (p1 → p5))) ∨ (p1 ∨ p5)) → (((p2 ∧ (((p5 ∨ False) ∨ ((p5 ∧ p3) ∧ p4)) ∧ p4)) ∧ True) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133775709070736802650009570388 : ((((False ∧ ((False ∨ p5) ∧ False)) ∨ (((p4 ∨ (((True ∧ p2) ∨ (p3 ∧ (p4 ∧ p4))) → p2)) ∧ True) ∨ p5)) ∧ False) ∨ (False → (p5 ∧ p1))) := by
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
theorem thm_5_vars_319046639561767327777613602748 : (p4 ∨ (((((p5 → p4) ∨ (True ∧ False)) ∧ (p4 ∨ p5)) → (p4 → (p3 → (((p1 ∧ False) ∨ p1) ∨ True)))) ∨ ((p1 → (p1 → True)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246603387034727030355111713574 : ((p5 ∧ p2) ∨ (p3 ∨ (p1 → (((p2 ∨ (p2 ∨ (p1 ∧ (((True ∧ True) ∨ p4) ∨ (p2 → ((p5 ∨ p4) → p3)))))) ∨ p1) ∨ (False → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208342434307816896155872778819 : (((p4 → False) ∧ (p4 → (p3 ∧ p1))) → ((True → (p4 → (p5 ∧ (((p4 ∨ ((False → p1) ∨ (p1 → p1))) ∧ False) ∨ p2)))) ∨ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42383389000649449244917936336 : (((p4 ∧ ((True ∧ ((((p3 ∨ True) → False) ∨ ((False ∧ p4) ∨ (p4 ∨ p3))) ∨ ((p2 ∧ p3) ∨ False))) → (True → (p3 ∨ p3)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44401018019548944783796020303 : ((((((p4 ∨ ((p3 → False) ∨ (p1 → True))) ∨ (p1 ∧ (False → True))) ∧ True) → ((((p4 → p4) ∨ p3) ∧ (p5 → False)) ∨ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135221023095726848751980954411 : ((((((p3 → ((False ∨ p2) ∨ (p3 ∧ False))) ∨ p2) ∧ p4) ∨ (((True ∨ p2) ∧ p3) → (p3 → p5))) → (p4 ∧ True)) ∨ (p1 → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181593310620646646503518811249 : ((p1 → ((p2 ∧ p4) → (p5 → (True ∨ ((p1 ∧ (p2 ∨ p1)) → p2))))) → (((p1 ∧ ((p4 ∧ (False ∨ (p2 ∧ p4))) ∨ p1)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117459751926714852967783923436 : ((p1 ∧ ((p1 ∨ p5) ∨ ((((p1 ∧ False) ∨ p2) → p4) ∨ (p5 ∨ ((((True → (p2 → p1)) ∨ False) ∨ False) → (True → p5)))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323792189921674681644173980873 : (p5 ∨ (((((p1 → p3) ∧ ((False ∧ p4) → (p5 ∨ (False ∨ p2)))) → p4) → (p1 ∨ (p2 ∧ p4))) ∨ ((p1 → p1) → ((False → p2) ∨ True)))) := by
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
theorem thm_5_vars_208429758453310916815344893302 : (((p4 ∨ p1) ∨ ((p2 ∨ p2) ∧ p1)) → ((((True ∧ p5) ∧ True) ∧ (p4 → ((True ∨ False) ∨ p1))) ∨ (False ∨ (p5 ∨ ((p3 → True) ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626457937792763712282827000807 : ((((p4 → ((((False → (p3 ∧ True)) → ((p1 ∨ p1) → (p5 ∧ (True ∨ p3)))) → (((p5 → (p1 → p1)) → p4) → p5)) → p2)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_62097707847231011007552832941 : ((p2 ∧ (p5 ∧ (((((p3 ∧ ((p2 → p1) ∨ p2)) ∧ ((p2 ∧ p2) ∨ p2)) ∧ (p4 ∧ p4)) → ((p1 → p5) ∨ p4)) ∧ (p3 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700192516218505628803486910811 : (((((p4 ∨ p1) ∨ (((p4 → False) → (p5 ∧ (True ∨ False))) ∧ p4)) → ((((True ∨ p4) ∨ False) ∨ (p2 ∨ (p4 → (True ∧ p5)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306157176759061313681081380652 : (p1 ∨ (((p3 ∨ False) ∨ p2) ∨ (True → ((p2 ∨ True) ∨ (((p4 → ((p5 → False) → p1)) ∧ p4) ∧ (((True ∧ (p1 ∨ p1)) → p3) → False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147255234260781499584990611595 : ((((p4 ∨ (((p5 ∧ (((False → False) ∨ ((True ∧ (p5 ∨ p4)) ∨ False)) ∧ p2)) ∧ p3) ∨ p5)) ∧ False) ∨ True) ∨ (p5 ∨ ((p5 ∧ False) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731329467885654351197591828868 : ((((p4 ∨ (p1 → True)) → ((((((False → p2) ∧ (p4 → (p2 → p3))) ∧ p2) ∨ p1) ∧ (False ∨ (p2 → p3))) ∧ ((p1 ∧ True) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338140794772404356340829674175 : (p1 → ((False ∧ (p4 ∧ (False ∨ (False ∨ (p4 ∧ p4))))) ∨ (((((p5 ∨ False) → False) ∨ (p3 ∧ (p4 ∨ p5))) ∨ p5) ∨ ((True ∧ p3) ∨ p1)))) := by
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
theorem thm_5_vars_178859387031815399412771343166 : (((p2 ∨ (p4 → p3)) → ((p2 ∧ (p2 ∧ False)) ∨ (p2 ∨ (p5 ∧ p3)))) ∨ ((p4 ∧ (False ∧ ((p1 ∧ (p3 ∨ False)) ∧ (False ∨ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157334112239769374491930697002 : (((p1 ∨ ((p3 ∨ (((p3 → p1) ∧ (p5 → ((p4 ∨ p1) ∧ (p5 ∧ p2)))) → False)) → p4)) → p4) ∨ ((p5 ∨ (p3 → p2)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225813630010455762440673766820 : (((True ∧ p1) ∨ p5) ∨ ((False ∧ ((False ∨ (p3 ∨ (p2 ∧ p2))) → (p5 → (p1 ∨ ((p2 ∧ True) → (p5 → p5)))))) ∨ ((p1 ∧ p5) → p1))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774233167349105565422116871054 : (((False ∨ ((((p3 → ((((p2 ∨ p5) ∧ p4) ∧ True) ∨ p3)) → (((True ∨ (p1 ∧ p1)) ∧ p4) ∧ p3)) ∧ False) ∨ ((p1 → p3) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681613684736445845566318145079 : ((((p2 → ((True → ((((p1 ∧ True) ∧ p2) ∧ p3) → True)) ∨ (((True → (True ∧ p4)) ∧ False) ∧ p3))) → (((p5 ∨ True) ∨ p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138561549328579916981719073729 : ((((((((p5 ∨ p1) ∨ p5) ∧ (p4 → (((p5 ∧ True) → (True → p1)) ∧ (p3 ∨ p4)))) ∨ p2) ∨ p3) → False) ∧ True) → (p3 → (True → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((((p5 ∨ p1) ∨ p5) ∧ (p4 → (((p5 ∧ True) → (True → p1)) ∧ (p3 ∨ p4)))) ∨ p2) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



