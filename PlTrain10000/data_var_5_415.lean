variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310861935765468060295231031150 : (p2 ∨ (((p4 → p5) → p1) → (p5 ∨ ((((((True ∨ (((p1 ∧ True) ∧ True) ∧ True)) ∨ p4) ∧ p3) → p4) → p2) → ((p5 ∧ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_694729532367712700758671170567 : ((((p3 ∨ ((((p2 ∧ p5) ∧ False) ∧ p1) ∨ ((p4 ∨ p4) ∨ (p4 ∨ p1)))) ∨ (((True ∨ p1) ∧ ((False ∨ (p2 ∨ p4)) → p4)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186108576695933121908261143111 : ((((((p3 ∧ False) ∧ (p2 ∨ p5)) ∨ p1) → (False ∧ p2)) ∨ False) → (p5 → (True ∧ (((True → p2) ∧ p3) ∨ (((p3 ∨ False) → True) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623751877900428087523306492864 : ((((p1 ∨ ((((((p4 ∧ (p1 ∨ p4)) → p4) → True) ∨ p4) ∨ (((p2 ∧ p4) → False) ∧ False)) ∧ ((p1 → p1) → (False ∨ False)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213142541979913379389941119924 : ((((p5 → p1) ∧ p4) ∧ True) ∨ ((p2 ∨ (((p2 → (p1 → (p3 ∨ p1))) ∨ True) ∧ (p3 ∧ (True → (p2 ∧ p5))))) ∨ (False ∨ (p4 → True)))) := by
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
theorem thm_5_vars_68271093543816962481738043286 : ((p3 → ((True → ((p1 ∨ (((p1 ∧ (p4 ∨ True)) ∨ p5) ∨ p2)) ∨ ((p2 ∧ (False ∧ (p1 → (False ∧ p3)))) ∨ True))) ∨ (p1 ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747763826017414858490268325882 : ((((False → p1) → (((p5 ∨ ((p2 → ((p2 → p3) ∧ (((False ∧ p3) ∧ True) ∧ (p5 ∧ False)))) ∧ p3)) → p4) ∨ ((True → p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111496573634550701470869820427 : (((p3 → ((p4 ∨ p2) ∧ ((False ∧ (p2 ∨ ((p5 → p4) → (p3 ∧ ((p2 → ((p3 ∧ True) ∧ p4)) ∧ p2))))) ∧ p3))) ∧ p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358641217350449401159618200612 : (p5 → (p4 → (((True ∧ (p2 → ((True ∧ ((p5 ∧ p2) ∨ True)) ∨ (((True → False) ∨ (((p3 ∧ p1) ∨ p5) ∧ p1)) → True)))) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111527616963175528679770269350 : ((((((p3 → p5) → (p1 ∧ (p5 ∧ (p3 ∨ ((p3 ∨ ((False ∨ False) ∧ (p1 ∧ (p3 → p4)))) ∨ p4))))) ∧ False) ∧ p5) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115506946535831178711018285093 : ((((p3 → ((p1 → p1) ∨ p3)) ∧ (False ∨ p1)) → (True → ((False ∧ (p3 ∧ p1)) ∨ ((((p2 ∨ False) → False) → False) ∨ p4)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186619360898107241077907008588 : ((((p4 ∧ p5) ∨ (p3 → ((True → True) → p3))) → (False ∧ p2)) → ((p4 ∨ ((True → (((p3 → True) → (p2 ∨ p2)) → False)) ∨ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p5) ∨ (p3 → ((True → True) → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66218794250477505513424308730 : ((p5 ∨ ((p2 → ((p2 ∨ p5) ∧ (p5 ∨ ((p5 ∧ p1) ∨ (p5 → p3))))) → ((p1 → ((p1 → p2) ∧ p1)) → (p2 → (p3 ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_249561311290835981682257905883 : ((p5 ∨ p2) ∨ ((p2 ∧ ((p4 → p4) → False)) ∨ (((True ∨ p3) ∧ True) ∨ (True ∨ ((((((True ∧ p4) ∧ p4) ∨ p2) → p1) ∨ p5) ∨ p3))))) := by
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
theorem thm_5_vars_310809477657853661421555215140 : (p2 ∨ ((False ∨ (p5 ∧ p4)) ∨ ((p5 ∧ (((p5 ∨ (False ∧ p1)) ∨ p4) ∨ ((((p1 → False) ∨ p2) → p2) ∨ ((p3 → p2) ∧ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335696189931433945266573965480 : (p1 → (((((((True ∨ (True ∧ ((False ∧ p3) → (p4 ∧ False)))) ∨ p1) ∨ (True → p4)) → p5) ∨ ((p5 → (p4 ∧ False)) → p2)) ∨ p1) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200325367660463271335520857544 : (((False ∨ True) ∧ (p5 → ((p5 ∨ True) ∨ p3))) → (p1 → ((p4 → False) ∨ (((p2 → ((False ∧ p2) → p2)) ∨ (True → p5)) ∨ (p4 ∧ True))))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166674145501355941653188479375 : ((p2 → ((p1 ∧ ((p5 ∧ ((((p1 ∨ p2) → p1) ∨ p4) ∧ (p3 ∧ True))) ∨ p1)) → False)) ∨ (p1 ∨ (((p4 → True) ∨ p4) ∧ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678421505288450065954458080448 : (((((p2 → (p5 ∧ (p1 ∧ p2))) ∧ (p4 ∧ (p3 ∨ ((((False ∨ True) → True) ∧ (True ∧ p1)) ∧ p4)))) ∨ ((p1 ∧ (p2 ∧ False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150291042130616044975262192191 : ((p4 → (((p1 → p5) ∨ ((((False → (((p2 ∧ p5) → p5) ∧ (True ∧ p4))) ∧ p4) ∧ p1) → p1)) → p3)) ∨ ((p3 ∧ p1) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200938099594361023695669998987 : ((p1 ∨ (p4 ∨ (p1 → (True → (p5 → False))))) → (((True → (True ∨ (p4 → (p2 ∧ p4)))) ∧ (p3 ∧ p5)) ∨ (False → (p5 → (p1 ∨ p3))))) := by
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
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299259075946854385281085673675 : (False ∨ (((False ∨ ((((True → p3) ∧ (((False ∨ True) ∨ p5) ∨ (p2 → True))) ∨ p4) → (p1 → False))) ∨ ((p3 → (p3 ∧ p2)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49260793068208707777333620098 : (((p1 ∧ (((p4 ∨ p4) ∧ (((False ∨ ((p2 ∨ True) ∨ False)) → (p1 ∨ ((True ∨ True) ∨ p5))) → p2)) ∧ p2)) ∨ ((False ∧ p1) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_158253705057821046568057198225 : ((((p3 ∧ True) → False) ∨ (((((p4 ∧ p2) → p4) ∧ False) ∨ p5) ∧ (p4 ∧ ((p4 ∨ p5) ∨ p3)))) ∨ ((False ∨ p5) → ((False ∨ True) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140299395506751590628091100687 : ((((p4 → p1) ∧ (((((p3 ∧ p1) ∨ True) ∨ (((p1 → p2) ∧ p4) ∨ p3)) ∨ p1) ∨ p3)) ∧ (p1 ∧ (p3 ∧ p4))) → ((p2 → p5) ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h3.left
          let h13 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h3.left
          let h18 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h3.left
          let h26 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h3.left
          let h31 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h3.left
      let h36 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h3.left
    let h41 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621847043811572829883248866943 : ((((p1 ∧ ((p5 → ((True ∨ ((p4 → True) → False)) ∧ (True ∨ p4))) ∧ (((False ∨ (p5 ∧ (p2 ∧ (False → True)))) ∨ p1) ∧ p3))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_327972610218106487693500011959 : (True → (((((p5 ∧ False) ∧ p5) → p4) ∧ (((((((p2 ∨ True) ∧ p2) → p5) ∧ p1) → (p1 → (p3 ∨ False))) ∨ True) → False)) → (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((((p2 ∨ True) ∧ p2) → p5) ∧ p1) → (p1 → (p3 ∨ False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177248881437377184976826191396 : ((False ∨ ((((p3 ∧ False) ∨ p3) ∨ (((p5 ∨ True) ∨ False) → p4)) ∨ True)) ∧ ((False ∨ (False → p1)) ∨ (((p2 ∨ False) ∨ (True ∨ p1)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233045115037559079203458928070 : ((p4 ∧ (True ∨ p5)) → ((((p2 ∧ p3) ∨ p1) → p2) ∨ ((p3 ∧ p1) → (((p2 ∧ p2) ∨ (False → p5)) → (((True ∧ p1) ∧ False) ∨ p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h16.left
      let h22 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h16.left
      let h25 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135345160695314443263259860564 : (((True ∧ (True → (p2 ∨ (((((False ∨ p3) ∨ (p5 → p2)) ∧ (p5 → p2)) → p4) → p5)))) ∧ ((False → True) → p3)) ∨ ((p1 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721291796893772997527450995186 : (((((False → p5) → (p2 → p2)) → (((p4 → ((((False ∧ (p2 → False)) ∧ False) ∧ (p3 → False)) → p4)) → ((p2 → p1) ∨ False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598777664300339337726223929240 : (((((p1 ∧ p3) ∧ (True ∧ (((((p3 ∨ ((p1 ∨ (True → p2)) → p5)) ∨ True) → (True → (False ∨ True))) ∧ (p3 ∧ p3)) ∨ p5))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59572275987726305440455803411 : (((p3 → p5) ∨ (((False ∨ (False ∨ False)) ∧ p2) ∨ ((p3 → (p2 ∨ ((True ∧ (((p2 → p1) → p4) ∨ p4)) ∨ False))) ∨ (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66736658716625489807752518051 : ((True → ((p2 → p2) → ((False ∨ ((p4 ∧ ((p4 ∧ (p3 ∧ False)) ∧ False)) ∨ (False ∨ ((p3 ∧ p2) ∨ (False → (p3 → p2)))))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322387434123516622736716492323 : (p5 ∨ ((((p1 → ((p1 → ((((False → p1) ∨ p3) ∧ p4) ∧ True)) → (False → p4))) ∨ p4) → (((p2 → p1) ∨ (False → p4)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185681250139963336016213971456 : ((p1 → ((True → (True → True)) ∧ ((False → (p1 ∨ False)) ∧ False))) ∨ ((((p4 ∨ ((p4 ∧ p1) → ((False → p3) ∨ True))) → p4) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42919260975859354172281432803 : (((p4 → (((((False ∨ p1) ∧ p4) ∨ (((p2 → ((p1 ∨ (True ∧ p2)) → (True ∧ p4))) ∨ (False ∨ p2)) → p2)) ∨ p5) ∧ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_486227534597620292776741672909 : (((((p1 ∨ p4) ∨ (p5 ∧ (p2 → p2))) ∨ (((False → ((p1 ∧ p1) ∧ False)) → False) → (p1 → (False ∨ (True ∧ ((p1 ∧ False) ∧ p5)))))) ∧ True) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((p1 ∧ p1) ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703919774894251815505188564996 : (((((True ∨ (p5 → ((p1 ∨ p4) → (False ∨ p2)))) ∨ p2) → (((((p2 ∧ ((p1 → p3) → p1)) ∧ p1) ∨ p5) ∨ (p4 ∧ p5)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233545530888781225545333396597 : ((p1 ∨ (p4 ∨ p5)) → (((p4 ∨ p4) → ((p3 → True) → (p3 ∨ True))) ∨ ((((((p2 ∨ False) ∨ False) ∧ p3) ∧ (p5 ∨ p1)) → p2) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41135945231709211921134299470 : ((((((((p3 ∨ (((p5 ∨ False) ∨ p1) ∧ (p4 → True))) → False) ∨ (p2 ∧ True)) ∨ p1) ∧ (True → False)) ∨ ((True ∨ p5) ∨ False)) ∨ p4) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_685285164513972649164513522162 : ((((p2 → ((((p3 ∨ (p4 ∨ p1)) ∧ (((p1 → (p5 → p2)) ∨ False) ∨ p5)) ∧ p3) ∧ p1)) ∨ ((p2 ∨ (True ∧ p5)) → (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113547180918076132700178173073 : ((((p5 → (p1 ∨ p4)) ∧ (((p4 ∧ ((False → (p1 ∧ (p1 ∧ p2))) ∧ p4)) ∨ (p1 ∨ p2)) ∨ (p3 ∧ p1))) ∨ (True ∨ p1)) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_479194014298011980108261328565 : (((((((False ∧ p5) → True) → True) ∨ (False → p4)) ∧ ((((p2 → True) → False) ∧ p4) ∨ ((p3 ∨ p2) ∨ (p4 → ((p2 ∧ p5) → True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112362666223943023465098887813 : (((((p3 ∨ (p3 ∧ ((((((((p1 → p5) ∨ (p3 ∨ p5)) ∨ p2) → p3) ∨ p2) ∧ p4) ∨ False) → p4))) ∨ p3) ∧ p3) → p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53371564911399110961704083286 : ((((((((p4 ∨ p2) ∧ False) ∧ (p3 ∨ p4)) → True) ∧ False) → p3) → (p3 ∨ ((p1 ∨ ((((p4 → p5) ∨ False) ∨ True) → p4)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172787258837886274029173561599 : (((False → False) → (p1 ∨ ((((p3 → False) → ((p5 ∧ p4) ∧ p3)) ∧ p1) ∨ True))) ∨ ((p4 → p4) → (p5 ∧ (False ∨ ((p5 ∨ p3) ∨ False))))) := by
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
theorem thm_5_vars_164541902319065048382315858500 : (((((p4 ∨ p3) → ((p3 ∧ False) ∧ (p1 ∨ False))) ∧ (p4 → ((p2 ∧ p1) → p1))) ∧ p5) ∨ (False → (True ∧ ((p2 ∧ (p3 ∧ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342325383818284832089302508972 : (p2 → (((True → (((True ∨ p3) → False) ∧ p1)) ∧ (p2 ∨ ((((p4 ∨ p2) ∨ p3) ∨ p4) ∨ p1))) → (((True ∧ p2) ∨ False) ∧ (p1 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h29 =>
            -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
            have h30 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h16, we can now drive its conclusion.
            let h31 := h16 h30
            -- We need to get the left conjuct of h31 based on <expert-advice>.
            let h32 := h31.left
            -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
            have h33 : (True ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h32, we can now drive its conclusion.
            let h34 := h32 h33
            -- False on the left can always be used.
            apply False.elim h34
        case inr h35 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h36 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h37 := h16 h36
          -- We need to get the left conjuct of h37 based on <expert-advice>.
          let h38 := h37.left
          -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
          have h39 : (True ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h38, we can now drive its conclusion.
          let h40 := h38 h39
          -- False on the left can always be used.
          apply False.elim h40
      case inr h41 =>
        -- One of the premise coincides with the conclusion.
        exact h41
    case inr h42 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h43 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h44 := h16 h43
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
      have h46 : (True ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h45, we can now drive its conclusion.
      let h47 := h45 h46
      -- False on the left can always be used.
      apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57356325091902538258692780302 : (((p3 ∧ (p4 ∨ False)) ∨ (((((True ∨ p3) → ((((False → p1) ∧ ((True ∨ p4) → p5)) → p4) ∨ True)) ∨ p4) ∨ (p2 ∧ True)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327809404037885773777843050483 : (True → (((p3 → (True ∧ (p1 ∧ (((False ∨ p4) → (p2 ∧ p4)) → (p5 ∧ (((p5 → p4) ∨ (p5 → p5)) ∨ p3)))))) ∨ True) ∨ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86547415359457833396554613406 : ((((True → (((p1 ∨ p3) ∨ p1) ∧ p2)) ∧ p2) ∧ ((p1 ∧ p1) → ((((p5 ∨ False) → False) → (((p4 ∨ p1) → p1) → p2)) → False))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (((p5 ∨ False) → False) → (((p4 ∨ p1) → p1) → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h13
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h19 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h18
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h19
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : (((p5 ∨ False) → False) → (((p4 ∨ p1) → p1) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h24 := h20 h21
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592793344048271510268965042335 : ((((((p3 ∧ (((p1 ∨ (False ∧ p5)) ∧ (p2 ∨ (p1 ∧ p2))) ∧ ((False ∨ p4) → p1))) ∨ (p5 ∧ p2)) ∧ ((p3 ∧ True) ∧ True)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206866955109745725093818848746 : (((((p2 ∨ p3) → p1) ∧ p3) ∧ p5) → (((p1 ∨ True) ∧ (True → ((p2 ∧ (p5 ∧ (p3 ∨ p3))) ∧ p4))) ∨ (p1 → (p4 → (p5 ∨ p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630207371774626255955458192457 : ((((((p4 → True) ∨ (((False ∧ (True → False)) ∧ ((True ∧ False) → p3)) → ((((p5 ∨ p5) → (p2 ∨ p3)) → p3) → p3))) ∨ p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110967694221334037643194722594 : ((((p2 ∨ ((p5 → (((p1 ∧ p2) ∧ (True → (((p2 ∧ p3) → p3) ∧ (p2 → True)))) ∨ p2)) ∨ p4)) ∨ (True → p5)) ∧ p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53983490227950395720589163942 : (((((p5 → (p1 ∧ (False → (p5 ∨ True)))) → True) ∨ True) → ((((p5 → p3) → ((p5 ∨ (p2 → (p4 ∧ p2))) ∨ p2)) → p2) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_677924053646681235759859790072 : (((((p5 → ((p1 ∧ ((p2 ∧ p5) ∨ (p3 → ((p2 ∧ p1) → (p4 → p3))))) ∨ p4)) ∨ (p4 ∧ True)) ∨ (((p3 → p4) ∧ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315756494454674414399407804186 : (p3 ∨ ((True ∧ p1) → (((((p5 ∧ (True → p3)) ∧ (p4 ∨ (True ∨ p3))) ∧ ((p5 ∧ p2) → (p3 → (False ∨ p5)))) → (p4 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252872445174170982164483017293 : ((True ∧ p1) → (((p5 ∨ ((p3 → (False ∧ p2)) → (((p1 ∨ ((p5 → ((True ∧ (p2 ∨ p3)) ∨ False)) → p5)) → p5) ∨ p1))) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172586541852011038477102585072 : ((((p3 ∨ True) ∨ p1) → (((((p2 ∨ (p5 ∧ p5)) ∧ p3) ∨ p2) ∨ True) → p2)) ∨ (False → (((p3 ∨ False) ∧ p3) → ((p5 → p2) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113434541140475026227245789172 : (((((True ∧ ((p1 → p1) → ((p4 ∧ ((((p3 ∨ p1) ∧ p3) ∧ (p3 ∨ p4)) ∨ p3)) → p3))) → p2) ∨ p3) ∨ (p2 ∨ p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39666173298502109324356668419 : (((p3 ∨ (p3 → (((p2 ∨ False) ∨ p1) → (((p5 ∨ p5) ∨ ((((p5 ∨ (p3 ∧ False)) ∧ p4) ∧ p1) → p4)) ∨ (p5 → p5))))) ∧ True) ∨ p1) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386000257140644943333565797496 : ((((((False ∧ ((False ∨ (p2 ∨ ((((p1 → p1) ∨ (False ∨ p2)) ∨ (False ∨ p4)) → p2))) ∧ (p3 → p5))) ∨ p5) ∨ (True ∧ True)) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223773644099237623903478595792 : ((p2 ∨ (p3 → True)) ∧ (p4 ∨ ((p1 ∧ ((((p2 ∧ p1) ∨ p5) ∧ False) ∧ p3)) ∨ (p1 → ((True ∧ p1) → (p5 → ((p2 → p3) ∨ p1))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41661456611313639338942996124 : ((((p5 ∨ (True ∧ ((True ∧ True) ∧ False))) ∧ ((((p3 ∨ p2) → ((p5 → p5) → (p1 ∧ ((p5 ∧ True) ∧ p1)))) ∨ p4) ∧ False)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349334791848433830619340457658 : (p3 → (p3 → (((False ∧ ((p4 → ((True ∨ p1) ∨ (((p5 → p2) ∧ p3) → (p2 ∨ p1)))) ∧ (True ∧ (False ∨ p5)))) ∨ (p1 ∧ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65055704528647312620077644056 : ((p2 ∨ (p2 ∧ (((((p3 ∧ ((True → ((True → p5) ∨ (p3 → p2))) → p2)) ∨ p3) ∧ False) ∨ (p1 ∧ ((p1 → p5) ∨ p1))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329492325779229621637584532423 : (True → ((p3 → p3) ∧ ((p2 ∨ (((p4 ∨ p2) ∧ ((((((p2 ∧ p4) → (p3 → p1)) ∨ p5) ∨ p3) ∧ False) ∧ (False ∨ p1))) ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701823460686565042667534380716 : ((((p4 ∧ ((p5 ∨ ((p3 ∨ p3) ∧ p4)) → (False ∨ p1))) ∧ (p2 → ((((p3 → (((p1 ∧ True) ∨ p2) ∧ False)) ∨ False) ∨ False) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111382981288599096895568266640 : (((False ∨ ((((False → ((p5 ∨ p4) ∨ ((((True → p2) ∧ p1) ∧ p3) → False))) → False) → (p1 ∨ p3)) → (False ∨ p2))) ∧ p5) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619835820885791863311376064269 : (((((p3 ∨ p2) ∧ (p1 ∧ ((p1 ∧ (((p3 → p4) ∧ p5) → ((p4 → (p5 ∨ (False ∧ (p4 ∧ (p2 ∨ p3))))) → p2))) ∨ p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_328642102021980358832373531362 : (True → (((((p5 ∧ (True ∨ False)) → ((True ∧ p3) ∨ p5)) → p3) ∨ (p4 → True)) → ((((p2 ∨ p2) ∨ p1) ∨ True) ∨ (p5 ∧ (p5 → p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355836547804560559693081658307 : (p5 → (((((((p4 ∧ p2) ∨ p4) ∧ (p2 ∧ p3)) ∨ (p2 → (p2 ∨ (p2 ∧ (p4 → p1))))) ∨ (p5 ∨ False)) ∨ p4) ∨ ((p4 ∨ True) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757091995382699208636786471691 : (((p1 ∧ ((False ∨ (False ∧ p3)) ∧ ((p2 ∨ p5) ∨ ((False → (((False → True) ∧ p1) ∨ ((p3 ∧ True) → ((p1 ∧ p3) ∨ p3)))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651313567064112006446564105941 : ((((((p4 ∧ p4) ∧ p3) ∨ ((p1 ∧ (p3 ∧ (False ∨ (((p2 ∧ p3) → p5) ∨ p3)))) ∧ (p2 → ((True → True) → True)))) ∧ (True ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54425105069846527941218296100 : (((((p2 → (False ∧ (False → p3))) → p3) ∨ p1) ∨ (False ∧ ((p4 ∨ p1) → ((p4 → p5) ∧ (p5 ∧ ((True ∨ (p4 ∨ p3)) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662143307369959607935527069992 : (((((((p1 ∧ (False → p5)) ∨ ((True ∨ False) ∨ p2)) ∨ (p1 ∨ p5)) → (((p3 ∨ True) ∨ p3) ∧ ((False ∧ False) ∧ p5))) → (True → False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ (False → p5)) ∨ ((True ∨ False) ∨ p2)) ∨ (p1 ∨ p5)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61133982301166937960183677193 : ((False ∧ (((p4 ∧ (((p4 → True) ∧ p2) → p2)) → True) → ((((p1 ∧ ((p1 ∧ False) ∨ (p2 ∨ p2))) → (p5 ∧ p3)) ∨ p1) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153531001218037256495282950796 : ((True → (((p1 ∨ ((((p2 → False) → False) → p5) ∨ ((p1 → False) ∨ False))) ∧ (p3 ∨ p3)) ∧ (p5 ∧ True))) → (((False ∨ False) ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67724543834385752258876674953 : ((p2 → ((((p4 → ((p5 ∧ p2) ∧ (p2 → True))) ∧ ((p2 ∧ p3) → (True ∧ p4))) ∨ (((p2 → (p3 ∧ p4)) ∧ p3) ∨ p2)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300782338681902382640771036632 : (False ∨ (((((p3 → (False → p1)) ∨ (p2 → (True → p3))) ∧ p5) → (False ∨ (True ∧ p1))) ∨ ((p1 → (False → (p1 ∨ True))) → (False → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325098747537858146988179486447 : (p5 ∨ ((p2 → p1) → (False ∨ (((p3 ∨ p3) ∧ ((p2 ∨ (False → p4)) → (((p3 ∧ False) ∧ (p1 → True)) ∧ ((p1 → p5) → False)))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ (False → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ (False → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h13
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- We need to get the left conjuct of h16 based on <expert-advice>.
    let h17 := h16.left
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54592222705632627161759513831 : (((p5 ∨ (False ∨ ((False ∨ (p2 → p3)) ∨ False))) ∨ (False ∧ ((((False ∧ ((True → ((False ∧ p4) ∧ p4)) → p2)) → p5) ∧ p5) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689145965971418127674438061622 : (((((((p3 ∨ p5) → ((p1 ∨ (p1 ∨ (p5 ∨ p2))) → (True ∨ p3))) ∨ p5) → p1) ∨ ((p3 → p1) ∨ (((p5 → p5) ∨ False) ∨ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191067597839369568379914827385 : (((p4 ∨ ((p2 ∨ True) ∧ p4)) → ((p1 ∨ False) → p2)) ∨ (p5 ∨ (p3 → (((p2 ∨ (False ∨ (p1 ∨ p5))) → p2) ∨ (False ∨ (True ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692805896738741734871772998232 : ((((((False ∧ p2) → p4) ∧ (False ∧ (p1 ∧ ((p5 ∧ (p1 ∧ False)) ∧ p5)))) ∧ ((True ∧ (p3 ∧ (p3 → (False ∨ (p4 → False))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112886166145456051209086928765 : ((((True ∨ True) ∧ (p2 ∧ ((p1 ∨ ((False ∧ (False → (p2 → p5))) ∧ p2)) ∨ ((True ∨ p4) ∧ ((False → p1) ∨ p5))))) → p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186030809101273885474594284160 : ((((((p4 ∧ (True ∨ (True ∨ p4))) ∧ p3) → True) ∧ p4) ∨ p5) → (False ∨ (((p5 → ((False ∧ p3) ∨ p1)) ∧ (p4 → p2)) → (p1 ∨ p2)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309343552786457176845852449044 : (p2 ∨ ((((((((p4 ∧ ((p1 → False) → p3)) ∧ p1) ∨ p2) → False) ∨ (True ∧ True)) → p3) ∧ (p1 ∨ ((p3 → p4) → False))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173144129040699231732185286584 : ((p3 ∨ (((p5 ∧ p5) → (p3 ∨ ((p5 → True) → (p5 → False)))) ∧ (p1 → p5))) ∨ (((p2 ∨ True) → (True ∨ p1)) ∨ ((p5 → p2) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197962513855748515923171703925 : (((p5 ∧ p1) ∧ ((True ∧ (p5 ∨ p1)) ∨ p1)) ∨ ((False ∧ (p3 → (p5 ∨ False))) → (((p5 ∧ p4) → (True ∧ False)) → (p2 ∨ (p1 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326857239541431073692890283443 : (True → (((p3 → ((((((True ∧ (p4 → (((p5 ∧ p5) → p2) ∧ p3))) ∨ p4) → ((p1 ∨ p1) ∨ p4)) ∧ False) ∨ p1) ∨ p2)) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47446626326794301206107395104 : (((p3 ∧ ((p5 → p4) ∨ ((p3 → (p5 ∧ ((p3 → (p2 → (p2 → p5))) ∨ (p5 ∧ (p1 ∧ (p1 ∧ p3)))))) ∨ p5))) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244103389458126354499305261258 : ((True ∧ p3) ∨ ((True → p2) → (((p3 → (True → p1)) ∨ ((((p4 ∨ True) ∧ p4) ∨ p1) → (p2 → (p4 → ((p3 ∨ p1) ∨ p2))))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134333469655671637988631195187 : (((p3 ∧ ((p1 ∨ (p4 ∧ (p2 → True))) → ((p4 ∨ (True ∧ (((p5 ∧ p3) ∧ p3) ∧ p3))) ∧ (p4 → p2)))) ∨ p5) ∨ (p5 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262434787755330083489720157229 : (True ∧ ((p4 ∧ ((True ∨ (p1 ∧ ((p2 ∨ p4) → (p5 → True)))) ∧ (((p3 ∨ (((False ∧ p1) → p1) ∧ (True ∧ p1))) → p1) → p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178272177031956596360464512154 : (((((p5 ∨ False) ∧ False) ∨ (((False ∨ p5) → True) ∧ True)) ∧ (p5 ∨ p3)) ∨ ((False ∨ (p4 → (p3 → (p4 ∨ ((p5 ∧ p5) ∨ p5))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_562985051681567226478153626750 : (((p5 ∨ ((p4 ∨ (((False ∨ p4) ∧ (False ∧ p1)) → (p5 ∨ p4))) ∧ (((p3 ∧ (p4 ∧ p2)) ∧ p2) ∨ (p5 → ((True → p2) → p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383174433924044198753926500227 : (((((p2 ∨ ((True ∧ ((p5 → p3) ∧ (p2 → p1))) ∨ ((p2 ∧ p3) → (((p4 ∧ (p2 → p5)) ∧ (p4 → p4)) ∨ p5)))) ∨ False) ∨ True) ∧ True) ∧ True) := by
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



