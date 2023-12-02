variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54560264576512414444956363758 : (((p3 ∧ (p1 → ((p2 → (True ∨ p3)) → p3))) ∨ (((False ∨ (p4 ∧ (((((p2 → p3) ∧ False) ∧ p1) ∨ p2) ∧ True))) ∨ True) ∨ p3)) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163084476845518641576267361588 : (((True → ((p2 → p4) ∧ (True → (((p4 ∧ p3) → p3) ∧ False)))) → (p3 ∨ (p4 ∧ p5))) ∧ (True ∨ ((p5 → ((p4 ∧ p4) ∧ True)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115144060106110255849959669293 : (((p3 ∧ ((p1 ∨ ((True ∧ p3) ∧ ((p3 → True) ∨ p2))) → p2)) → (((p3 ∧ (p1 ∨ p4)) ∨ p5) ∧ ((p4 ∧ p4) → False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49160897230101815942890205189 : (((((((p4 → True) → p2) → p1) → p2) ∧ ((p4 ∧ p1) ∨ ((p3 ∨ p1) ∨ (p2 ∨ ((True ∨ True) → False))))) ∨ (True → (p1 → True))) ∨ p5) := by
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
theorem thm_5_vars_341094922339435431618957270186 : (p2 → ((p2 → ((p1 ∧ False) ∨ ((((p2 → False) → ((((p1 → False) ∧ p4) ∨ p3) ∨ True)) ∧ (p3 ∨ (True ∨ False))) ∨ (True → p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66474010706572900455557405950 : ((True → (((p2 ∨ ((p3 ∧ ((((p2 ∧ (False ∨ p2)) ∨ p5) → (p2 ∨ p4)) → p1)) ∧ ((p1 ∨ (True ∨ p5)) → p1))) ∧ False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178597361299970613879797351625 : (((((p4 ∧ p5) → p1) → (p2 ∧ p4)) ∨ (p5 → (p2 → (p2 → p3)))) ∨ ((((p5 ∧ (p3 ∨ (False ∧ p5))) → (p4 ∨ True)) ∨ p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136702886798311190192725222710 : (((p1 ∧ p1) ∧ ((p1 ∧ (((p4 ∧ (p2 ∨ (p3 ∨ ((p3 → (p1 → p5)) → p4)))) ∨ (p4 ∨ p3)) → p2)) → p2)) ∨ (False → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254159753156636440406043692502 : ((p2 ∧ p1) → ((((p1 → ((((p4 → (p5 ∨ (p2 → p4))) → (p3 → ((p2 ∧ p5) → False))) ∨ True) ∨ p5)) ∧ p1) ∨ p2) ∨ (False ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596222662898159697186509691052 : (((((((p5 ∧ p4) ∨ p2) → ((p5 ∧ p5) ∨ True)) ∧ (p3 ∧ (((True → ((p4 → p1) ∨ (False ∧ p1))) ∧ (p5 ∨ p2)) ∨ p3))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299208057939543902676545167646 : (False ∨ (((p5 ∧ ((p2 ∨ (True → (p4 ∨ (p4 → (((p3 ∨ p4) ∨ p5) ∧ (p2 ∨ p2)))))) → (p1 ∧ (False ∨ True)))) ∧ (True ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118755814788799309689605892055 : ((p5 ∨ ((p3 ∨ p2) ∧ (p1 ∧ (p5 ∧ (((True → p2) ∧ p5) → (p3 ∨ ((True → p5) → ((p4 → p5) ∧ (p1 ∧ p5))))))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67845953344212736250731944911 : ((p2 → ((True → ((p5 → ((True ∧ ((p1 ∨ ((p3 ∨ (p4 ∨ (p4 ∧ (p4 ∧ p1)))) ∨ True)) → p2)) ∨ p3)) → p4)) ∨ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61421713338257867341752297915 : ((p1 ∧ ((((p1 ∨ p1) → ((True ∨ False) ∧ ((p4 ∨ ((p2 → True) → (p3 ∨ (True → (True ∨ True))))) ∧ False))) ∨ (p5 ∧ p2)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94288177726760704554437043543 : ((p2 ∧ ((((p1 ∨ (((False → p4) ∨ p1) ∨ (True → True))) → (p2 → False)) ∧ ((True ∨ p3) ∧ p4)) ∧ (((p1 → p4) ∨ p5) ∨ p4))) → p5) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : (p1 ∨ (((False → p4) ∨ p1) ∨ (True → True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h15 := h6 h13
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : (p1 ∨ (((False → p4) ∨ p1) ∨ (True → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h20
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h28 : (p1 ∨ (((False → p4) ∨ p1) ∨ (True → True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h30 := h6 h28
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h35 : (p1 ∨ (((False → p4) ∨ p1) ∨ (True → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h37 := h6 h35
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- False on the left can always be used.
      apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742753089244074746553888740085 : ((((p3 → False) ∨ ((p1 ∨ ((False ∨ (p5 ∨ False)) ∨ (True ∧ (p3 → ((((False ∨ p2) → p3) ∨ p1) ∨ (True ∧ (p2 ∧ p2))))))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233056776530654398275962033893 : ((p4 ∧ (p2 ∨ True)) → ((((p2 ∧ (((((False → (p2 ∨ p2)) → p3) ∨ p1) → (p3 ∨ ((p1 ∨ p3) ∧ p5))) ∨ False)) ∧ p1) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_184022372849634839141939334618 : ((((p5 → (p1 ∨ ((p5 ∧ False) ∧ (p1 ∨ p3)))) ∨ p2) ∨ True) ∨ (((p1 ∨ ((p2 ∧ False) → (p3 ∨ p4))) → (p1 ∨ p2)) ∨ (p2 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37148121402930405621755744771 : (((((p4 ∧ ((p2 ∨ (p4 ∨ (p2 ∧ (p4 ∨ (True ∨ (True → (p1 ∨ (p1 ∨ p5)))))))) ∨ p4)) ∧ (p4 ∨ (True ∨ p4))) ∧ p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64986855239705043859452053627 : ((p2 ∨ (((p2 ∨ p2) ∧ p1) ∧ (p4 ∨ (((((p4 ∧ (p4 ∧ p4)) ∨ p3) → p3) ∧ (p1 ∧ (p2 ∧ True))) → ((p5 ∨ True) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307291732798116261346573196124 : (p1 ∨ (p2 ∨ (p2 → ((p4 ∨ (p4 ∨ (((((p1 ∨ ((True ∧ p3) ∨ p1)) ∨ (False ∧ False)) → p5) → ((False ∨ p4) ∨ p4)) ∨ p1))) ∨ True)))) := by
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
theorem thm_5_vars_152036801234730987648020746212 : ((((p3 → p2) → ((p4 ∧ False) ∧ (p2 → (p3 ∨ True)))) ∧ (True ∨ (p4 ∨ (False → (False ∨ (p3 → p5)))))) → ((p2 ∧ (p3 → p3)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p3 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : (p3 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h21 : (p3 → p2) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h23 := h5 h21
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184853753353572405356596113548 : ((((p5 ∧ p3) ∧ p1) ∧ ((p1 ∨ p2) → (False ∧ (p1 ∧ p1)))) ∨ ((p5 → (p3 → True)) → ((False ∧ p5) ∨ (((True → p1) → p5) → True)))) := by
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
theorem thm_5_vars_87007114792470832175393795544 : (((((False ∨ ((True → p1) → False)) ∧ p4) ∨ True) → ((((p2 ∨ p1) → (p4 → (p2 ∨ True))) ∨ ((p5 ∨ (True ∨ False)) → True)) ∧ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ ((True → p1) → False)) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135036129480557597985623937566 : (((((p4 → ((p1 → (p2 ∨ False)) ∧ p3)) → (((False ∨ (p2 → (p1 ∨ p4))) → True) ∧ p2)) ∧ p1) ∨ (p5 ∧ p4)) ∨ (p3 → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51290760099913924035879825462 : (((p4 ∧ ((p2 ∨ p5) ∨ (((p1 ∧ (p3 → p5)) ∧ p3) → (((p4 ∧ p2) → p4) → False)))) ∨ ((p4 ∧ ((p4 ∨ p3) ∧ p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194090882413692194167254351682 : ((True → (p4 ∨ (((p3 ∨ (p5 ∨ p2)) ∨ p1) ∨ p4))) → ((((True → p1) ∨ (p1 → (p2 → p2))) ∨ (((True ∨ p3) ∨ p1) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200808955217971383687490995523 : ((p5 ∧ (((p5 ∧ p5) ∧ p3) ∨ (p3 ∧ True))) → ((((p4 → p1) ∨ True) → ((p3 ∧ (p2 ∧ p4)) ∨ ((p5 ∧ p2) ∧ (p1 ∨ p2)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781769706319801210464705888965 : (((p2 ∨ (p5 ∨ ((p4 ∨ True) → (((((p2 ∨ p4) ∨ (((True → (p1 ∧ p5)) ∧ p1) → True)) ∨ (p1 ∨ (p1 → p3))) → False) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797413425838415796876704567063 : (((p1 → ((False ∧ ((((p2 ∨ (p2 ∨ (p5 ∨ (False ∨ ((p3 → (p2 → (p1 ∧ p3))) → p4))))) → (p5 ∨ p1)) ∧ p5) ∨ p4)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67448151244443371887171619575 : ((p1 → (((((p4 → p5) ∧ (p1 ∨ (p2 ∧ (p2 → p3)))) ∧ p4) ∧ (p2 ∨ (True ∧ ((p3 ∨ p1) ∨ p3)))) → (p4 ∧ (p5 ∧ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h29 := h2.left
  let h30 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h31.left
  let h34 := h31.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h35 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h36 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h37 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h38 := h33 h37
      -- One of the premise coincides with the conclusion.
      exact h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h44 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h45 := h33 h44
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h46 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h47 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h48 := h33 h47
          -- One of the premise coincides with the conclusion.
          exact h48
      case inr h49 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h50 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h51 := h33 h50
        -- One of the premise coincides with the conclusion.
        exact h51
  case inr h52 =>
    -- Conjunctions on the left can always be decomposed.
    let h53 := h52.left
    let h54 := h52.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h55 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h56 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h32
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h57 := h33 h56
      -- One of the premise coincides with the conclusion.
      exact h57
    case inr h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Disjunctions on the left can always be decomposed.
      cases h60
      case inl h61 =>
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h63 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h64 := h33 h63
          -- One of the premise coincides with the conclusion.
          exact h64
        case inr h65 =>
          -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
          have h66 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h33, we can now drive its conclusion.
          let h67 := h33 h66
          -- One of the premise coincides with the conclusion.
          exact h67
      case inr h68 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h69 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h70 := h33 h69
        -- One of the premise coincides with the conclusion.
        exact h70
  -- Conjunctions on the left can always be decomposed.
  let h71 := h2.left
  let h72 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h73 := h71.left
  let h74 := h71.right
  -- Conjunctions on the left can always be decomposed.
  let h75 := h73.left
  let h76 := h73.right
  -- Disjunctions on the left can always be decomposed.
  cases h76
  case inl h77 =>
    -- Disjunctions on the left can always be decomposed.
    cases h72
    case inl h78 =>
      -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
      have h79 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h74
      -- We have shown the premise of h75, we can now drive its conclusion.
      let h80 := h75 h79
      -- One of the premise coincides with the conclusion.
      exact h80
    case inr h81 =>
      -- Conjunctions on the left can always be decomposed.
      let h82 := h81.left
      let h83 := h81.right
      -- Disjunctions on the left can always be decomposed.
      cases h83
      case inl h84 =>
        -- Disjunctions on the left can always be decomposed.
        cases h84
        case inl h85 =>
          -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
          have h86 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h74
          -- We have shown the premise of h75, we can now drive its conclusion.
          let h87 := h75 h86
          -- One of the premise coincides with the conclusion.
          exact h87
        case inr h88 =>
          -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
          have h89 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h74
          -- We have shown the premise of h75, we can now drive its conclusion.
          let h90 := h75 h89
          -- One of the premise coincides with the conclusion.
          exact h90
      case inr h91 =>
        -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
        have h92 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h74
        -- We have shown the premise of h75, we can now drive its conclusion.
        let h93 := h75 h92
        -- One of the premise coincides with the conclusion.
        exact h93
  case inr h94 =>
    -- Conjunctions on the left can always be decomposed.
    let h95 := h94.left
    let h96 := h94.right
    -- Disjunctions on the left can always be decomposed.
    cases h72
    case inl h97 =>
      -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
      have h98 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h74
      -- We have shown the premise of h75, we can now drive its conclusion.
      let h99 := h75 h98
      -- One of the premise coincides with the conclusion.
      exact h99
    case inr h100 =>
      -- Conjunctions on the left can always be decomposed.
      let h101 := h100.left
      let h102 := h100.right
      -- Disjunctions on the left can always be decomposed.
      cases h102
      case inl h103 =>
        -- Disjunctions on the left can always be decomposed.
        cases h103
        case inl h104 =>
          -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
          have h105 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h74
          -- We have shown the premise of h75, we can now drive its conclusion.
          let h106 := h75 h105
          -- One of the premise coincides with the conclusion.
          exact h106
        case inr h107 =>
          -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
          have h108 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h74
          -- We have shown the premise of h75, we can now drive its conclusion.
          let h109 := h75 h108
          -- One of the premise coincides with the conclusion.
          exact h109
      case inr h110 =>
        -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
        have h111 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h74
        -- We have shown the premise of h75, we can now drive its conclusion.
        let h112 := h75 h111
        -- One of the premise coincides with the conclusion.
        exact h112



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113792752460249413563299885735 : ((((p1 ∧ True) ∨ (p5 → (True ∨ ((p4 ∨ (False ∨ (((p4 → False) ∨ p5) ∧ ((p5 ∧ True) → p4)))) ∧ p2)))) → (False ∧ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112844718435223059899806712520 : (((((p4 ∨ p2) ∨ p1) ∧ (((p4 → (p1 ∨ True)) → (((p1 → p4) ∨ p1) → (True → (p4 ∨ (p4 ∧ p2))))) ∧ p4)) → False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315439235781313120155317236873 : (p3 ∨ ((p4 ∨ (p4 ∨ False)) ∨ (True ∧ (p1 ∨ ((((((p5 ∧ p4) ∧ False) ∨ False) ∧ (True ∨ p3)) ∨ False) ∨ ((p2 ∨ True) ∨ (False ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137966821459318713028461256925 : ((p5 ∨ (((p4 → ((p2 ∧ (True ∨ p3)) → (False → ((False → p3) ∧ (p2 → p1))))) ∨ p3) → (p3 ∨ (p3 ∧ True)))) ∨ ((True ∨ p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178680476489383045767798227568 : (((p3 → (p4 ∨ (p5 ∧ p5))) ∧ (((p1 ∨ p3) ∨ (p2 ∧ p2)) ∧ True)) ∨ (((((p4 ∨ p4) ∨ (p1 → False)) ∨ True) → (p2 ∧ p4)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p4) ∨ (p1 → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804821269693698393115429982084 : (((p3 → ((p3 ∧ p2) ∧ ((((p2 ∨ p5) ∧ p2) → False) → (((((p2 → p3) ∧ p3) ∨ (True ∨ p5)) → p2) ∨ (True → (p2 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54686152031475706213048917662 : ((((p1 ∧ (True ∨ (p3 ∨ (True ∧ True)))) → True) → (p5 ∨ ((True ∧ (((p4 ∧ (True → p2)) ∨ (p4 → (p4 ∧ p3))) → p1)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240448361107440114586995322814 : ((p5 ∨ True) ∧ ((((p1 ∨ ((True ∧ p2) ∧ p3)) → False) ∧ p4) ∨ ((p2 ∧ (((True ∧ ((p5 → True) ∨ p1)) ∧ p5) ∧ (True → False))) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310621620152584742861753238247 : (p2 ∨ (((False → (p3 ∨ True)) → p4) ∨ ((p5 ∨ ((True ∨ p5) → True)) → ((p2 ∧ (((p5 → False) → p3) ∨ (False → p1))) ∨ (p3 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_61949673186032895752866638639 : ((p2 ∧ (((((((p3 → False) ∨ ((p4 ∨ p5) → p1)) ∨ False) ∨ p1) ∨ p3) ∨ p4) ∧ ((p1 ∧ p2) → ((p1 ∨ p4) ∨ (p4 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135553741353532811037396782492 : (((True ∧ (((p1 → ((False ∨ p4) → p3)) ∨ ((p3 ∨ (p4 → p4)) ∧ p1)) → False)) ∧ (((p2 ∧ p2) ∨ p2) ∨ p2)) ∨ ((p2 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339515103561971641286868744729 : (p1 → (False ∨ ((p4 ∧ p5) ∨ ((p4 ∧ True) ∨ (p2 → (False ∨ ((((p1 → ((False → p1) → p3)) → True) ∨ p5) → ((True ∧ p1) → p2)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250688317485469592335902611190 : ((p1 → False) ∨ (((((p5 → p4) ∨ p4) → (p1 → p4)) → (((p4 → p1) ∧ False) ∧ ((((False ∨ p4) ∨ False) ∧ (False ∧ p5)) ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736349436936297393175159432246 : ((((False → p5) ∧ (((p5 → (p5 → (False → (((p5 ∧ True) → (False → True)) ∧ (p2 ∧ (True ∧ p4)))))) ∨ False) → (p1 ∧ (False ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313257200601538801332730622981 : (p3 ∨ (((p5 → p4) → (p3 → ((p4 ∨ ((True ∨ ((p3 ∧ p1) ∧ p3)) ∧ (p1 → ((p1 → (p2 → (p1 → False))) → p4)))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128747572488456182171761426488 : (((((p4 ∨ (p5 → (p4 ∧ (p2 ∧ (p5 → (p2 ∨ p3)))))) → (p5 ∨ p5)) ∨ (((p3 → p5) ∧ False) → True)) ∧ True) ∧ (p5 ∨ (p2 → p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353433579152622804116993047389 : (p4 → (p1 ∨ (((p3 → (p2 → p4)) → ((p1 ∧ (p1 ∨ (p5 → p3))) ∨ True)) ∨ ((p2 → (((True ∧ (True → True)) → False) → False)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171624429449434448293748638512 : ((((p5 ∧ (p5 ∨ p5)) ∨ (p5 ∨ ((p1 → p2) ∨ ((True → p4) → p5)))) ∨ p2) ∨ (((True ∧ ((p3 ∨ p1) ∧ (p3 ∧ True))) ∧ True) → p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658704043621785867128251285737 : ((((p4 ∨ ((p3 ∨ False) ∧ ((False ∧ (p4 → False)) ∧ ((((p2 → (p3 → p3)) ∨ (p1 ∨ p4)) ∧ p4) ∧ (p1 ∨ p4))))) ∨ (p2 → True)) ∨ p5) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204092046372354073282512214191 : ((p5 → (p2 ∨ ((p3 → True) ∨ True))) ∧ ((p4 ∧ ((((False ∨ p4) ∧ (False ∧ False)) ∨ (p4 → (p4 ∧ p3))) ∨ (p4 → (p4 ∧ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301361804647562454153057506460 : (False ∨ (((True ∨ (True ∧ p1)) ∧ p5) ∨ ((((p4 ∧ (True ∧ (p4 ∨ ((p5 → True) ∨ True)))) ∧ (p4 ∨ p3)) ∨ (True ∧ (p3 ∨ True))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28254259297242743714114549440 : ((True ∧ (((p3 → ((p5 ∧ p4) ∧ False)) → ((True → False) ∨ (((p3 ∧ ((p3 ∧ p2) ∨ True)) ∨ (p5 ∧ False)) → p1))) ∨ (p5 ∧ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315880855601388146517292650394 : (p3 ∨ (True ∧ (((((p5 ∧ p4) ∨ (p5 ∧ (p3 ∨ ((p3 ∨ False) ∨ p3)))) ∨ ((p1 → p5) → p2)) ∨ ((p1 → (p2 → p2)) ∧ True)) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564883732169382951162553679558 : (((True → (((((p4 ∨ p3) ∨ p1) ∧ (p1 ∨ p2)) → (((p3 ∧ p5) ∧ (p1 ∧ p5)) ∧ ((p2 ∧ p3) ∨ (p1 ∨ (p2 ∨ True))))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150853146277117520164846982560 : (((((p2 ∧ (p5 → p1)) ∧ (((p2 ∨ p2) ∧ p4) ∨ False)) ∨ ((False → (p2 ∧ (p1 ∧ True))) ∨ p5)) ∨ p4) → (((p1 → p1) → p5) → p5)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : (p1 → p1) := by
            -- Implications on the right can always be decomposed.
            intro h14
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h13
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : (p1 → p1) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h17
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h23 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h23
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h28 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h30 := h2 h28
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200763098744927260181314009438 : ((p4 ∧ (((False → p3) ∨ (False ∨ p3)) ∨ True)) → ((True ∧ (((p4 ∧ (True ∧ True)) → ((p3 → p3) ∧ ((p2 ∨ p1) → p1))) ∧ p4)) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115871017414281215506545288465 : (((((p5 ∨ p5) ∧ p5) ∧ p1) ∨ (((True → (((((p5 ∧ False) → p2) ∨ p3) ∧ p2) ∧ p1)) → (p1 ∨ False)) ∨ (p3 → p1))) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119431372479693748414770983164 : ((p4 → ((((((False → p5) ∨ p2) ∧ (False ∨ ((p4 ∧ p4) ∧ p1))) → ((p3 ∧ True) ∨ p3)) ∨ True) ∨ (p4 ∧ (p1 ∧ True)))) ∨ (p5 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657405011467853371711427397385 : (((((p3 → p2) ∧ (p4 ∨ (((((((True → p3) ∨ (p4 ∨ (p5 → p1))) → True) → p3) → p3) → p2) ∨ (p3 ∨ p1)))) ∨ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187530462823147919207313979031 : ((p1 ∨ (True → (True ∧ ((((p2 → p2) ∧ p5) ∨ p1) ∨ p4)))) → ((((p2 ∨ p3) ∧ (p4 ∧ (True → p3))) ∧ p5) ∨ (p5 ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112744427140050259458094313225 : ((((p4 ∧ (((p1 ∨ True) ∨ (p1 ∧ ((p3 ∧ p1) ∧ p3))) → p5)) ∨ ((p4 → p1) → ((p4 ∧ (p3 → False)) → True))) → p1) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217193544794811541619987080988 : ((((p2 ∨ True) → p2) ∨ p2) → (((p5 ∨ (p5 ∨ p1)) ∧ (((p2 ∨ p5) → True) ∧ (p5 → False))) → (p2 ∨ (p5 ∨ (True → (False ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h4.left
      let h13 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h4.left
      let h18 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119550254690755319996312944308 : ((p5 → (((p5 ∧ (True ∨ p3)) ∧ (((((False ∨ True) ∨ (False ∧ p5)) ∧ (True ∧ p1)) ∨ p2) ∧ p4)) ∨ (False ∨ (p5 ∨ False)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251573126546632279956343581234 : ((p3 → False) ∨ ((True → False) → (False ∨ ((p3 ∧ p2) → (False ∧ (p5 ∧ ((p1 ∧ p4) ∧ (((p1 ∧ p4) → (p5 ∧ p3)) ∧ (p5 → p2))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_192171108325862443618731491159 : ((((p1 → (((p3 → p5) → p4) ∨ True)) ∧ p3) ∧ p5) → ((True → ((False ∨ (False ∨ (p4 ∨ p2))) ∧ (((False ∨ p5) ∨ p4) → p2))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774245392701107239181161758236 : (((False ∨ ((((False ∨ (False ∨ (p1 ∧ False))) ∧ (p2 → ((p1 → p2) → ((p4 ∨ p3) ∨ p4)))) ∨ (p2 ∧ p1)) ∨ (False → (True ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47458338047192902564362045434 : (((p4 ∧ (p1 ∧ ((p2 → (p2 ∨ p1)) → ((False ∨ p1) ∧ ((p3 ∧ True) ∨ (True ∧ (((p3 ∨ False) ∨ p2) ∨ p1))))))) ∨ (False ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211390088465791515334387332235 : (((False → p4) ∨ (p3 ∨ False)) ∧ (((((((p3 ∨ p3) → True) ∧ p1) → True) ∨ False) ∧ ((p4 ∧ ((p5 ∧ p2) → p2)) ∨ p2)) → (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149567790593517542489752607469 : ((p2 ∧ (p3 ∧ (((p2 ∨ p1) → ((p3 → True) ∨ (p2 ∨ (False ∧ False)))) ∧ ((p4 ∧ True) ∨ (p5 ∧ True))))) ∨ (p3 ∨ ((p2 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116191803041296365575197678883 : ((((p3 ∧ p1) ∧ True) ∨ (False ∨ (p5 ∧ ((((p5 → p4) → False) ∧ (((p4 → (p4 ∧ p3)) → p2) ∨ p5)) ∨ (p2 ∧ p4))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177785466738301463524137447464 : (((p5 ∧ (((p4 → (p4 ∧ p2)) ∨ (p4 ∨ p4)) ∨ (p3 ∧ True))) ∧ p3) ∨ ((((True ∧ False) ∨ ((False → p3) ∨ (True ∨ False))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201329319996346764983402694997 : ((p5 → ((False ∨ (True → (p3 ∨ p1))) → True)) → (((((p3 → (True → False)) ∨ (p1 ∨ p1)) ∨ True) ∧ (p4 ∨ (p1 ∨ p1))) → (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157926257060841720563099789816 : ((((False ∨ (p3 ∧ (p4 ∧ (p1 ∨ False)))) ∧ p5) ∧ (False ∧ ((p4 ∨ ((False → p4) ∨ False)) ∨ p1))) ∨ ((((False ∨ p2) ∨ p3) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148367902457122520030145694854 : ((((p4 ∨ (p4 → (((p1 → (p3 ∧ (p1 ∧ False))) ∧ p1) → p4))) ∧ p4) ∨ ((p5 → True) → (False ∨ p5))) ∨ ((p5 ∧ (p4 ∧ True)) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230713971123864534806719085069 : (((p4 → p5) ∧ p1) → (((True → False) ∧ p1) → ((((p4 ∧ p5) ∨ p4) ∧ True) ∧ ((False ∧ True) ∧ (((True ∧ (False ∨ p5)) ∨ p1) ∧ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h14 := h9 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305968830448165909101996726139 : (p1 ∨ ((True ∨ (True ∨ (True ∧ True))) ∧ ((((False ∨ (p5 ∧ ((p2 ∧ (p4 ∧ p2)) ∧ (p5 ∨ False)))) ∨ p3) ∨ ((p2 → p2) ∨ False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47331176614050794744964269025 : ((((False ∧ p3) ∧ (((((p2 ∨ (False → ((p2 ∧ (p1 ∧ p4)) → p4))) ∧ True) ∧ p1) ∧ (p2 ∨ (p3 ∨ p4))) ∨ p3)) ∨ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60095564922238604844406513915 : (((p3 ∨ False) → ((p3 ∧ (p5 → p2)) → ((p2 ∧ ((p4 ∨ p5) ∨ (((True ∨ (False ∧ (p4 → p5))) ∧ p5) ∧ p1))) ∨ (True ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179880568421243625712619026403 : ((((((p4 → (p4 → True)) → (p4 ∧ (p2 ∨ p4))) ∨ p5) ∧ p5) ∨ p2) → ((((True ∧ (p4 → ((False ∨ True) ∨ True))) → False) → p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (p4 → (p4 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h7
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : (True ∧ (p4 → ((False ∨ True) ∨ True))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h14
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (True ∧ (p4 → ((False ∨ True) ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h19
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197052608251233476600118898922 : ((((p3 ∧ p3) ∨ (False ∨ (p4 ∨ p4))) ∨ p3) ∨ (p1 → (((False ∨ (True → p5)) ∨ p2) → ((p4 ∧ p3) → (p5 ∨ (False → (p4 ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356444882111110904323695860206 : (p5 → (((True → (p3 ∨ (p4 ∨ p3))) → (((p1 ∨ p3) ∨ p4) ∨ False)) ∨ ((((True ∧ ((p4 ∨ False) ∧ p1)) ∨ False) ∧ True) → (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66487907259472795558890219496 : ((True → ((((p4 ∨ p5) ∧ (p4 ∨ (True → (((p3 ∨ (p1 → (p3 ∧ p3))) ∨ True) ∨ p3)))) → ((p3 → (p2 → p4)) ∨ p5)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118373554048291306642746523467 : ((p2 ∨ (((p3 ∧ ((p1 → ((p3 → p3) ∨ (p4 ∧ (p1 ∨ (p1 ∧ p3))))) ∨ p5)) → p5) ∨ ((True ∧ p4) ∧ (p3 → p3)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783285572004792569813422283479 : (((p3 ∨ (((p2 → ((False → (((((p3 ∨ (p3 → True)) ∨ False) ∨ True) ∧ p5) ∧ p1)) ∨ True)) → p3) ∨ ((False ∨ False) → (p1 ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266120587932696450696983241778 : (True ∧ (p3 → (((((True ∧ ((p5 ∧ p3) ∧ p1)) ∨ (p4 ∨ True)) ∧ ((p3 → p1) ∨ p3)) ∧ (False ∧ (True ∨ (p2 → (p2 ∨ p1))))) ∨ True))) := by
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
theorem thm_5_vars_670790661535013559741390027258 : ((((p1 ∧ (((((((p2 ∨ p5) → (p1 ∧ ((p4 ∧ False) → True))) ∧ False) ∨ p2) → (p1 ∨ True)) ∧ p4) ∨ True)) ∨ (p4 ∨ (p3 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230973817624004529095683093778 : (((p4 ∧ p2) ∨ p3) → (((p3 ∧ (True → ((True ∨ p5) → (((p2 ∨ False) ∧ (p5 ∨ p5)) → ((p1 → (p3 ∧ p1)) ∨ True))))) ∧ p3) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
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
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797599468044019941637033177026 : (((p1 → ((((True ∨ (p5 → (p3 ∨ (p1 ∧ p2)))) ∨ (((False ∨ p2) ∨ (p3 ∨ True)) ∧ p4)) ∧ (p1 ∧ (p5 → (p5 ∧ p3)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156625693357118698396510769852 : ((((((p5 ∨ (True ∨ ((p4 → p4) ∧ ((p3 → p3) → p2)))) ∧ p1) → (False ∧ p1)) ∨ p5) ∧ True) ∨ (((p3 ∧ p4) ∨ True) ∨ (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909711040332705976132695361728 : ((((p5 ∧ ((((p4 → ((p4 ∨ (True → (p1 ∨ True))) → p4)) ∧ p2) → (p3 → p2)) → p1)) ∧ ((p4 → p3) → (p1 → (p3 ∨ p3)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 → ((p4 ∨ (True → (p1 ∨ True))) → p4)) ∧ p2) → (p3 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112886091005991123525235587916 : ((((True ∨ True) ∧ (((p3 → p2) ∨ (((((p5 → p5) ∧ p2) ∧ ((p2 ∨ (p3 → p1)) → p3)) → False) ∧ p1)) → p4)) → p4) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673926789306417485759982818029 : (((((p2 → p5) → (True ∧ (((p2 ∧ ((p4 ∨ (((p2 → (False ∨ False)) ∨ p3) ∨ p2)) ∨ p4)) ∨ p2) ∧ p2))) → ((True ∨ p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207208700992347984405895614131 : ((((p2 ∨ (True → p4)) ∧ True) ∨ p2) → (((p1 ∨ p4) → ((True ∨ (p2 → p5)) → ((p5 ∨ True) ∨ p2))) ∨ ((True → (p3 ∨ p4)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h23 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305156116615246015152020450933 : (p1 ∨ ((((p3 → (True ∧ (p2 ∨ (p2 ∧ p2)))) → (p4 → (False ∨ (True ∧ (p2 ∧ (p2 ∧ False)))))) ∧ p2) ∨ (True ∨ (True ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113246542898809627199838484000 : ((((p4 ∨ ((((p2 ∨ p4) → (p4 ∧ (False ∧ p3))) → (True → p5)) ∨ (p2 → (p5 ∧ p3)))) ∧ (False → p5)) ∧ (p1 ∧ p4)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805517960233923113551989964874 : (((p3 → (p4 ∨ ((((p1 ∧ (p2 → True)) ∧ p2) → (p3 ∨ (p1 ∨ ((True → p1) ∧ ((True ∨ (p5 → (p2 ∧ p4))) → p4))))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649623264199816863453015085049 : ((((((((p3 ∧ p1) → True) ∧ ((p3 ∧ True) ∧ p3)) ∧ (((False ∧ p1) ∨ p2) ∨ ((p5 ∧ False) → p3))) ∨ (p4 ∧ True)) ∧ (p2 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57080935308782260568308237933 : ((((False ∧ p4) ∧ p2) ∨ (((p4 → (((p5 ∨ (p3 ∨ (p3 ∧ False))) ∧ ((True ∨ p4) ∨ p2)) ∧ (p4 ∧ p2))) ∨ (False → p1)) ∨ False)) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340709007305355271346319368943 : (p2 → ((((((p2 ∧ ((p4 → p1) → p4)) ∨ p4) ∧ p3) ∨ ((p3 ∨ (False → True)) ∨ (((p2 ∨ False) ∨ p2) ∧ (p4 ∨ False)))) ∧ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



