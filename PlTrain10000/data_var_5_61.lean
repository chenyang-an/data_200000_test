variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340531730591224002779511407183 : (p2 → ((((p3 ∨ p2) ∧ p3) → (p1 ∨ ((((p5 ∨ ((p3 ∨ p4) ∧ p5)) ∧ p1) ∨ (False ∨ (p5 ∨ ((p1 ∨ False) ∧ True)))) ∨ True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344372164533099744416521807398 : (p2 → (p4 ∨ (((p1 → (((p3 → p2) ∧ p3) ∨ True)) → p3) ∨ (p4 → ((((False ∧ p3) → p1) → p4) → ((p2 ∨ p3) → (p3 ∨ p2))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157570779164650711320202855974 : (((((p1 ∧ p5) ∨ p2) ∧ (True ∧ ((False ∨ True) ∨ (((p3 → True) → p2) ∨ True)))) → (p1 → False)) ∨ (((p4 → True) → True) ∨ (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743726537760397137252756412074 : ((((True ∧ p3) → (p5 ∧ (False ∧ ((False ∨ (p3 ∧ ((p4 ∨ ((False ∨ True) ∧ True)) → (p1 → (False ∧ (True ∧ False)))))) ∧ (True ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345267512890102028123309308687 : (p3 → ((p5 ∨ ((False ∧ ((((p3 ∧ (p4 → (p5 → p4))) → p5) ∨ (False ∨ ((p2 → p3) → p1))) ∧ (False ∧ (p4 ∧ p5)))) ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59041167204108806847792844133 : (((p4 ∧ p2) ∨ ((((p4 → False) ∨ ((p1 → p5) ∧ ((((p4 ∧ (p5 ∨ True)) ∨ p2) ∨ (p4 → p4)) ∨ p2))) ∨ (p4 ∨ False)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655338301741297961530360798923 : (((((((((True → (p5 → p2)) ∧ False) → ((False ∧ ((p2 ∧ (p1 ∨ False)) → True)) → p5)) → p1) ∧ True) ∨ (p4 ∧ False)) ∨ (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601785770733719976616209419044 : ((((p4 ∧ (((p4 ∧ (((True ∨ p5) → p2) → ((((p2 ∧ (p4 → True)) ∧ True) ∨ (False ∨ False)) ∧ p3))) → p1) ∧ (False → p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356532655830213651015568786591 : (p5 → ((((p2 ∨ p4) → (p3 → p2)) → (p4 ∧ (p2 ∧ p4))) ∨ ((((False ∨ p3) ∧ (p1 → ((p4 → p3) ∧ p4))) ∨ (p4 → p4)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174757202467503679599237271713 : (((p5 → (p1 ∨ True)) → (p1 ∧ (((p2 → (p3 ∧ p4)) ∨ p1) ∧ (True → False)))) → ((p2 ∧ p3) ∧ (((p3 ∧ False) ∨ (p4 ∧ False)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (p5 → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
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
  -- Implications on the right can always be decomposed.
  intro h16
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260879241662513028920309069637 : ((p4 → True) → (p2 → ((p2 → ((p1 → (((p3 ∧ p1) ∧ (((p4 ∨ True) ∧ (False ∨ p1)) → p5)) → p4)) ∧ p1)) ∨ ((p4 → True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595121918550473666218439325662 : (((((((((p5 ∨ (p3 → ((p3 ∨ p3) ∨ p2))) ∨ p2) ∧ True) → p1) ∨ False) → (p5 ∧ (p4 ∨ (p5 → (p5 → (p1 → p1)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159352148920216982164233267317 : (((((((p4 ∧ False) ∧ p1) ∧ p3) ∨ ((((p1 ∨ p3) ∨ True) ∧ True) ∨ (p5 ∨ p3))) ∧ p1) ∧ p2) → (p5 ∨ ((p4 ∧ p2) ∨ (p1 ∧ p1)))) := by
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
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245415879595588591551701723539 : ((p2 ∧ p4) ∨ ((p2 ∨ (p5 → (False ∧ (p2 ∧ ((p1 → (((p4 → p4) ∧ (p4 ∧ (p4 ∧ (p2 ∨ p3)))) ∧ p2)) ∨ p5))))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61188370230611734667939909128 : ((False ∧ ((p2 → p4) ∧ ((((p3 → p5) → p3) ∨ ((p3 → (False → ((p5 ∧ (False ∨ (p2 ∧ (True ∧ p5)))) → False))) ∨ True)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231783212344842236899951875643 : (((p4 ∧ True) → p2) → ((p5 ∨ False) ∨ (p3 ∨ (p1 ∨ ((((((False ∧ (p4 ∨ True)) → p2) ∧ p3) → p1) → (p4 ∨ (p3 → True))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65466054774067910216099182223 : ((p3 ∨ (True ∧ ((((p5 ∧ p5) ∨ True) → (p4 ∧ ((True → p2) ∧ True))) → ((p3 → (((p1 ∧ p4) → p5) ∨ (p4 ∨ p1))) ∧ p2)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112273857778282241177125791719 : (((True → ((p4 ∨ (p5 → (((p3 ∧ True) ∨ (p2 → (p5 → (p1 ∨ ((p1 ∧ p2) → (True ∧ False)))))) ∧ p3))) ∨ p4)) ∨ p4) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46185160244312415992010799209 : ((((p1 ∧ ((((p2 → p3) ∧ (True → p5)) → ((p1 ∧ ((p2 ∨ p2) ∨ p4)) ∨ ((False ∧ False) ∧ p2))) → p2)) → p3) ∧ (p4 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340859439991365997801899927834 : (p2 → (((((True ∧ ((p3 ∧ (p4 ∨ (p2 → p4))) → False)) → (True ∨ (False → (p3 ∧ True)))) → p5) ∧ ((p1 → True) ∨ (p1 ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46630466580598006919897132580 : (((p4 ∧ ((True ∧ p2) ∧ (((p3 ∧ p1) ∧ (p4 ∨ (p2 ∨ (p5 → True)))) → (p2 ∨ ((p3 → (p4 ∨ p4)) → p2))))) ∧ (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263592728279792200229269921333 : (True ∧ ((p5 → ((False ∧ (((p2 ∧ p2) ∨ False) ∧ p2)) ∨ ((((p2 → True) → p5) ∨ (p4 ∧ p1)) → p1))) ∨ ((True → (p4 → p1)) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49179258786199792211700166708 : ((((((p3 → p2) ∨ p3) ∨ p3) ∨ ((p2 ∨ ((((False → p4) ∧ (p4 → p4)) ∧ True) → (p3 ∧ True))) ∨ True)) ∨ ((False ∧ p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51634205776067620236336674365 : (((((p5 ∨ (p3 ∧ (((p3 ∨ (p1 → p1)) ∨ (p5 ∧ p1)) ∨ p3))) ∨ p2) ∨ True) ∧ (((p5 ∧ ((True ∧ p1) ∧ False)) ∨ p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751123417069070821462755665359 : (((True ∧ (((p1 → p5) ∨ p1) ∧ (True → ((p1 ∧ p1) ∧ (p5 ∨ ((((p2 ∨ p4) ∨ True) ∧ p3) ∨ ((p3 ∨ p2) ∧ (p4 ∧ p3)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166167741710130559405612751166 : ((False ∧ ((p5 ∨ p3) ∨ (p2 → (p3 ∨ (p2 ∧ (((p3 → (p1 → p2)) ∧ False) ∧ p2)))))) ∨ (((((p5 → p4) ∨ p5) → p5) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797030179519540225685070081339 : (((p1 → ((((p4 ∨ (p5 → (((False → p2) → ((p2 → p3) → True)) → (True ∨ p1)))) → (p2 → (p2 ∨ p5))) → (p4 ∧ p3)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256589555309215616904980396727 : ((p1 ∨ True) → (((((((p4 ∨ p3) ∧ (p1 ∧ p5)) → p1) ∧ True) → False) → (p4 ∧ (p1 ∨ (p1 ∨ ((p4 ∧ False) ∨ False))))) ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((((p4 ∨ p3) ∧ (p1 ∧ p5)) → p1) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
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
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h4
    -- False on the left can always be used.
    apply False.elim h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((((p4 ∨ p3) ∧ (p1 ∧ p5)) → p1) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h20.left
        let h26 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h25
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h27 := h16 h17
    -- False on the left can always be used.
    apply False.elim h27
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h28 : ((((p4 ∨ p3) ∧ (p1 ∧ p5)) → p1) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h31.left
        let h34 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h31.left
        let h37 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h36
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h38 := h16 h28
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200739373435388732662113008393 : ((p3 ∧ ((p5 → False) ∧ ((p5 ∧ p4) ∨ p2))) → ((p1 ∨ p4) ∨ (p3 ∧ ((False ∧ (((((p2 ∨ p3) ∧ False) ∧ p1) ∧ True) ∨ False)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49865927275953709117655167633 : ((((p3 ∧ (p3 → ((((p1 ∨ (False ∧ (p5 → False))) ∨ (p4 → p5)) ∧ (p3 ∨ p4)) → True))) ∧ p3) ∧ ((p5 ∧ (False → p1)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53225200793608680446320272356 : ((((((p2 → False) ∧ True) ∨ p4) ∨ (True → ((p3 → p3) ∧ p3))) ∨ (((p3 ∧ p3) ∨ (False → p4)) ∨ (p5 ∧ (p1 → (p4 → p4))))) ∨ p3) := by
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
theorem thm_5_vars_302801587279361446042448127866 : (False ∨ (p5 ∨ ((((((True ∧ p4) → p2) ∧ ((p5 ∨ p1) → p4)) ∧ p5) ∧ ((p2 → p1) → (True ∨ ((True ∧ False) ∨ (p2 ∨ p2))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769035204316773236736698884604 : (((p5 ∧ ((p3 ∧ (p1 → p3)) ∨ ((((p4 → ((p4 ∨ ((p2 ∨ (False ∨ (p4 → p4))) ∨ (p4 ∧ p2))) ∧ True)) ∧ p3) → p5) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148209996523600870750208965880 : (((p4 ∨ (((p3 ∧ p3) ∧ (p3 ∧ False)) ∨ (((p2 → p3) → (p4 → False)) ∧ p1))) ∧ (True ∧ (p3 ∨ p4))) ∨ (True ∨ ((p3 → p2) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679150477314834282361267379317 : ((((p3 ∨ (True → ((((False → True) → p2) ∧ (p1 ∨ ((True ∨ ((p1 ∧ True) → False)) ∧ p2))) ∧ p5))) ∨ (p4 → (False → (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302662204203695936620946375583 : (False ∨ (p2 ∨ (p1 ∨ ((((p5 ∨ p4) ∨ (False ∨ ((((p3 → False) ∨ ((p2 → p5) → p2)) ∨ (p3 ∧ (p1 ∨ p4))) ∧ p2))) ∨ p5) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788411903856761125016593490987 : (((p5 ∨ ((((((p1 → (False → False)) ∨ (True ∧ p5)) ∧ (p5 ∧ p2)) ∨ p5) ∧ ((p1 → True) → ((p3 ∧ p2) → (p5 ∧ True)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42056892072645382318840286942 : ((((p2 ∨ p5) ∨ (p5 ∨ (((((p2 → p5) ∧ (((p3 → True) ∧ p4) ∨ True)) ∧ p3) ∨ p2) → (p2 → (p1 ∨ (p5 → p2)))))) ∨ p3) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41060725552788676805372093082 : ((((p1 ∧ ((p4 ∨ p1) → (((p5 → True) → ((((p2 ∧ False) ∧ False) ∧ (p5 ∨ p3)) → (False ∨ False))) ∨ p3))) → (p1 → p2)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345713417874896529783493278431 : (p3 → ((p1 → (p2 ∨ (((False ∨ (p2 ∨ p3)) ∧ (p5 ∧ p2)) ∨ (p3 ∧ (((p4 → p3) ∧ (True → p1)) ∨ (p2 ∨ (False ∧ p2))))))) ∨ p5)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682946558608900536987635613868 : (((((p2 ∨ p2) ∨ (p2 ∨ (((p5 ∨ p4) ∨ (False ∧ p2)) → ((p2 ∨ True) ∨ (p5 ∧ p4))))) ∧ (((p3 ∨ (True ∨ p2)) ∧ p5) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50656845840039079991992735366 : ((((p4 ∧ ((p3 ∨ p1) → ((p5 → p4) ∨ False))) ∧ (p4 → ((False → p3) ∧ (p2 ∧ (p1 ∨ p1))))) → (p5 ∧ (p2 ∧ (p2 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698286650796055740515783985585 : (((((((p1 → (p2 ∧ True)) ∨ (p5 ∧ p4)) → p3) ∧ (p4 → p2)) ∨ ((p2 ∧ (((p3 ∨ True) → (p4 ∨ False)) ∧ (p1 ∨ p4))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178061103297769206311855763250 : (((((True ∧ ((p1 → p2) ∨ (p3 → (p2 ∨ p4)))) → p5) ∨ p2) → p1) ∨ (((p5 → (p3 → ((p4 → p2) → (True → False)))) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234246280744368823695191334483 : ((False → (p3 ∨ p2)) → (p2 ∨ (((p4 ∧ (p1 → p3)) ∧ p1) → ((p2 ∨ (p2 ∨ ((True ∧ False) ∧ p5))) ∨ (((p5 ∧ p3) ∨ p1) ∨ p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304343457488389081659864525288 : (p1 ∨ ((((p3 ∨ (p4 ∧ p1)) ∨ (p2 ∨ ((p2 ∧ False) ∨ p3))) ∧ ((True ∨ p1) → ((True ∨ (((p5 ∨ p4) ∧ True) ∨ p4)) ∧ p2))) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h23 := h3 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323238627537346689780677241540 : (p5 ∨ ((((p4 ∧ p2) ∧ p4) → ((p5 → ((p2 ∧ p2) ∧ p2)) → ((True → p1) ∧ (False ∧ ((p4 → (False → True)) ∧ p2))))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225435736650130819582535903389 : (((p3 ∨ p4) ∧ p3) ∨ (p3 → ((((p1 ∧ p3) ∧ ((p3 → False) ∨ (p1 ∨ p5))) ∨ (((p3 → p1) → True) → (True → (p1 → p1)))) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302011489162226710028853695984 : (False ∨ (True ∧ ((((p1 ∨ (p4 → (False ∨ (((p2 ∨ ((False ∧ p1) → True)) → p3) → p4)))) → (p5 ∨ False)) ∨ ((p2 → True) ∧ p1)) ∨ True))) := by
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
theorem thm_5_vars_467091182367843923611326484432 : ((((((p3 → (((p3 ∧ (p5 ∧ p2)) ∨ (p4 ∨ p2)) ∧ p2)) ∧ p3) ∨ True) ∨ ((False ∨ (((True → True) → p4) → (p5 ∧ False))) → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167945016032515329094073275822 : (((p5 → ((p3 → p2) → ((p5 ∨ p5) → p3))) ∨ (((p3 → p3) ∧ (p5 ∨ p4)) → p1)) → ((p5 → (p4 ∧ p5)) ∨ ((p4 ∧ p3) → True))) := by
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
theorem thm_5_vars_155674630132004160740119801845 : (((p4 ∧ p1) ∨ (p1 → (((p4 ∧ p1) ∧ (((p3 ∨ (True → p3)) → p4) → (p1 → p3))) ∨ p1))) ∧ ((True ∨ p1) ∨ (p5 ∨ (False ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800160257435922427915925966653 : (((p2 → ((p5 ∨ (p4 ∧ ((((True → (p5 ∨ ((p5 ∨ ((True ∧ p1) ∧ p2)) ∧ p3))) ∨ (p3 → (p1 → True))) ∧ p2) ∧ p1))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208587526609273353912727093934 : (((p1 → p3) → ((p3 ∧ False) → p2)) → ((p2 → ((((p2 → p2) → (True → (p5 → (p3 ∧ p3)))) → p3) ∧ (True ∨ p2))) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118242417551314057609111243437 : ((p1 ∨ ((((False ∨ (p1 ∨ (p4 → (p1 → False)))) ∨ (p2 ∧ (p2 ∨ (p2 ∧ ((p3 → p1) ∧ p2))))) ∧ p5) ∨ (p5 → True))) ∨ (p1 ∨ p4)) := by
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
theorem thm_5_vars_318911085338487636556187676797 : (p4 ∨ ((((p3 ∧ (True ∨ (((p3 ∧ True) ∨ (p4 → ((((p5 → p4) ∧ p5) ∧ p1) ∨ p1))) → p5))) ∨ p5) ∧ p4) → (p2 ∨ (p3 ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117422289793527945956265603369 : ((p1 ∧ ((((((p4 ∧ True) → (((p5 → True) → p2) ∧ True)) ∨ (True → p1)) ∧ (False ∨ p3)) → p5) ∧ ((p1 ∧ p5) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111002740824901091769557824548 : ((((p5 ∧ (p5 ∨ (p5 ∨ ((p2 → True) ∨ (((p2 ∧ False) ∨ (False ∨ p2)) → (True ∧ False)))))) ∧ (p2 ∧ (p2 ∨ p4))) ∧ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232490171048135264360077808638 : ((True ∧ (True → False)) → (p1 ∧ ((p5 ∨ ((False ∨ ((False ∧ True) ∧ ((p3 ∨ (True → p1)) ∧ ((p2 ∨ p2) ∨ (p2 ∧ p3))))) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197963979465438133067486101407 : (((p5 ∧ p3) ∧ ((p4 ∨ p5) ∨ (p1 ∨ True))) ∨ (((False ∧ p4) ∧ ((p5 → p5) → (p1 ∧ (False ∨ (p3 ∨ ((p3 ∨ p5) ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197786563151826163569967663756 : ((((p1 ∧ p4) ∧ p2) ∨ (False ∧ (p1 ∨ False))) ∨ ((False ∧ (((True → ((p4 ∧ ((p4 ∨ p2) ∧ True)) → p5)) → (p2 → p4)) ∨ True)) → p4)) := by
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
theorem thm_5_vars_640393976559232217399759757019 : (((((True ∧ p5) ∧ ((False ∨ True) ∨ ((True ∨ ((((True ∨ p2) ∨ ((p1 ∨ (p3 → (True ∨ p4))) ∧ True)) → False) → False)) ∨ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227338877998386118417996167650 : (((p3 → False) → False) ∨ (((((False ∨ (True → (p5 → (False ∧ p2)))) ∧ p1) → (p4 ∧ ((False ∧ ((False ∧ p5) ∨ p1)) ∧ p5))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728142875001701768813459201723 : ((((p5 ∨ (p1 ∨ p3)) ∨ ((False ∧ False) ∧ ((p1 → ((p1 ∨ ((True → (p2 ∨ False)) ∧ (True ∧ ((p1 → p3) → p5)))) ∨ True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197808521644325100373991046004 : ((((p3 → p4) ∨ p3) ∨ ((False → p3) ∧ p1)) ∨ ((((p2 ∨ p2) ∨ ((p5 → p2) → ((p4 → p4) → (p5 ∧ p5)))) → (True ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256305719770165648212033486640 : ((False ∨ p1) → ((p1 → (False ∧ p5)) → (p3 → (((((p5 ∨ (False ∨ (p3 ∨ p4))) ∨ (p5 ∧ p3)) ∧ p2) ∨ (p1 ∨ p5)) → (False ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h12 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h13 := h2 h12
          -- We need to get the left conjuct of h13 based on <expert-advice>.
          let h14 := h13.left
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h21 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h20
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h22 := h2 h21
              -- We need to get the left conjuct of h22 based on <expert-advice>.
              let h23 := h22.left
              -- False on the left can always be used.
              apply False.elim h23
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h25 =>
              -- False on the left can always be used.
              apply False.elim h25
            case inr h26 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h27 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h26
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h28 := h2 h27
              -- We need to get the left conjuct of h28 based on <expert-advice>.
              let h29 := h28.left
              -- False on the left can always be used.
              apply False.elim h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h35 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h36 := h2 h35
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- False on the left can always be used.
        apply False.elim h37
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h42 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h41
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h43 := h2 h42
        -- We need to get the left conjuct of h43 based on <expert-advice>.
        let h44 := h43.left
        -- False on the left can always be used.
        apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h46 =>
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h48 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h47
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h49 := h2 h48
        -- We need to get the left conjuct of h49 based on <expert-advice>.
        let h50 := h49.left
        -- False on the left can always be used.
        apply False.elim h50
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h51.left
    let h53 := h51.right
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h56 =>
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h58 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h57
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h59 := h2 h58
          -- We need to get the left conjuct of h59 based on <expert-advice>.
          let h60 := h59.left
          -- False on the left can always be used.
          apply False.elim h60
      case inr h61 =>
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h62 =>
          -- False on the left can always be used.
          apply False.elim h62
        case inr h63 =>
          -- Disjunctions on the left can always be decomposed.
          cases h63
          case inl h64 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h65 =>
              -- False on the left can always be used.
              apply False.elim h65
            case inr h66 =>
              -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
              have h67 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h66
              -- We have shown the premise of h2, we can now drive its conclusion.
              let h68 := h2 h67
              -- We need to get the left conjuct of h68 based on <expert-advice>.
              let h69 := h68.left
              -- False on the left can always be used.
              apply False.elim h69
          case inr h70 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h71 =>
              -- False on the left can always be used.
              apply False.elim h71
            case inr h72 =>
              -- One of the premise coincides with the conclusion.
              exact h70
    case inr h73 =>
      -- Conjunctions on the left can always be decomposed.
      let h74 := h73.left
      let h75 := h73.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h76 =>
        -- False on the left can always be used.
        apply False.elim h76
      case inr h77 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h78 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h77
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h79 := h2 h78
        -- We need to get the left conjuct of h79 based on <expert-advice>.
        let h80 := h79.left
        -- False on the left can always be used.
        apply False.elim h80
  case inr h81 =>
    -- Disjunctions on the left can always be decomposed.
    cases h81
    case inl h82 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h83 =>
        -- False on the left can always be used.
        apply False.elim h83
      case inr h84 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h85 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h84
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h86 := h2 h85
        -- We need to get the left conjuct of h86 based on <expert-advice>.
        let h87 := h86.left
        -- False on the left can always be used.
        apply False.elim h87
    case inr h88 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h89 =>
        -- False on the left can always be used.
        apply False.elim h89
      case inr h90 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h91 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h90
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h92 := h2 h91
        -- We need to get the left conjuct of h92 based on <expert-advice>.
        let h93 := h92.left
        -- False on the left can always be used.
        apply False.elim h93



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47981924293253053515395398688 : (((((((((p5 ∨ False) → p4) ∧ p5) → (p5 ∧ p3)) ∨ (True ∧ p1)) → (p1 → False)) → ((p3 → p5) → (p1 → False))) → (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798927432300255519790292399720 : (((p1 → ((p5 → False) ∧ (((p3 → (p5 ∨ p2)) ∨ (((p1 → (p5 → p1)) ∨ p3) ∨ p4)) → ((p5 ∧ ((p3 ∧ p5) ∨ p1)) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316767656998732996025829537139 : (p3 ∨ (True → (True ∧ (p4 ∨ ((p3 → (((p1 ∨ (((p3 ∨ p2) ∨ p2) → (p2 ∧ False))) ∧ (p4 → False)) → ((p4 ∧ p3) ∨ p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69084738258845752524805490368 : ((p5 → (((p1 ∨ (True ∧ p1)) ∧ (((p5 → (p2 → (p1 → p1))) ∧ p3) ∧ ((True → ((p1 ∨ p1) → p1)) → (p3 → p3)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41515255244463727737501863848 : ((((((p5 ∧ p1) ∧ ((p3 ∨ p3) ∧ (p5 ∧ p4))) → p1) ∧ (((True → ((((p5 ∧ p1) → p1) ∨ p4) ∨ p3)) → p1) ∨ True)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652628120273055595025858402643 : ((((False ∨ (p5 ∨ ((((((False ∧ (p1 → p1)) ∨ True) ∧ p2) → False) → (False ∧ (((p4 ∨ p1) ∨ p3) ∨ False))) → p3))) ∧ (p2 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350060647826195227397049363762 : (p4 → (((True ∧ ((((p4 ∨ (True ∨ p3)) ∧ p2) ∧ ((p3 ∨ p5) ∧ ((((p3 ∨ p1) → False) → p2) ∧ False))) ∨ p4)) ∧ (p4 ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8574491412961834576438296634 : ((((((((True → (False ∧ (p1 ∨ ((p3 → p2) → p5)))) ∨ p2) ∨ p5) ∨ ((p3 ∨ (True ∧ p1)) ∧ p4)) ∨ True) ∨ (p5 ∧ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_118503625153033826352084616180 : ((p3 ∨ ((p5 → (((False → p5) ∨ (False ∧ p5)) ∨ p2)) ∧ (((((p5 ∧ p1) ∧ True) ∨ p2) ∨ (p5 ∨ p4)) ∧ (p4 ∨ p2)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134816514191072631548286295808 : (((True ∨ (True ∨ ((p1 → (p5 → (p2 ∧ (p3 ∧ (True → (p2 ∧ (p2 ∨ p2))))))) ∧ (p2 ∨ (p4 → p5))))) → p5) ∨ ((p3 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300955886052098577040554933095 : (False ∨ (((p5 → ((p4 ∨ True) ∨ (p2 → ((True ∨ p3) ∨ False)))) ∧ p5) ∨ ((False ∨ (p4 ∨ True)) ∨ ((p2 ∨ False) → (p1 ∨ (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_113020944255589167673894394543 : (((p5 ∧ (p3 → ((p2 ∧ (((p2 ∨ (p4 → (((p3 → p3) ∧ p4) ∧ (p1 ∨ False)))) ∧ p1) ∧ p1)) ∧ (p1 → p2)))) → p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46406115291417519881678901382 : ((((((p3 ∨ p1) ∧ p5) ∨ ((p5 ∧ p4) ∨ p5)) ∨ (p2 → (True → ((p2 → p5) ∨ ((p1 → p5) ∨ (p2 → p2)))))) ∧ (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114866490154510987586550730333 : (((((True → True) → ((p3 → True) ∨ (False → p2))) → (True → (p5 ∨ False))) ∨ ((((True → p5) → (p4 → p4)) → True) ∨ p1)) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354792218699128603612578989167 : (p5 → (((p3 → ((p3 ∧ (p4 → True)) ∨ p4)) ∧ (((((p3 → ((p2 ∨ p2) ∧ p5)) → False) ∨ (p4 ∨ p4)) → (p4 → p3)) ∧ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608207438542742654228185285468 : ((((((True → ((p4 ∨ ((p1 ∧ (True ∨ p5)) ∨ ((((p2 ∧ p2) → (p1 ∨ p5)) → (p4 ∨ p5)) ∨ p2))) ∨ p5)) ∧ p4) ∨ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_234896907817813044490426835340 : ((True ∧ True) ∧ (((p1 ∧ (p1 → ((((p5 → p4) ∨ (True ∨ (p3 ∧ p1))) ∧ ((p5 ∨ (p3 → (p1 ∧ True))) ∨ False)) ∨ False))) → p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40327102656427701584061913234 : ((((((True ∧ (False ∧ ((True ∧ p3) → ((p1 ∧ True) ∧ ((p1 → (p2 ∨ (p1 ∨ p2))) → (p2 ∨ p1)))))) ∨ p2) ∨ p1) ∨ True) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42315218101528262894672517633 : (((p2 ∧ ((True ∧ p4) ∨ ((((p4 ∨ True) ∧ (((p3 ∨ False) ∧ True) → (p2 → ((p4 ∧ p2) ∧ True)))) ∨ (p4 ∨ False)) ∨ p2))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49584442370058584195509643544 : ((((p5 → ((((p1 ∧ (p1 → (p1 ∧ True))) ∨ (False ∨ p4)) → False) ∧ p4)) → (((p4 ∨ p3) ∧ p2) → p3)) → ((p4 ∨ p1) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40816272066186493072702753636 : ((((p4 ∨ ((((((p4 ∧ p4) ∨ p3) ∧ (((False ∧ p3) ∨ p2) ∨ p4)) ∨ (p2 → (True ∧ True))) → p4) ∧ (False ∨ p1))) → p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651062473611768281536215789081 : ((((((True ∧ True) ∨ (p3 → p3)) ∧ (((True ∨ True) → p1) → (((p2 ∨ (False ∨ (p4 ∨ (p2 ∨ True)))) → p5) ∧ p3))) ∧ (p4 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302977759801253994657782011948 : (False ∨ (p1 → ((((False ∧ ((p4 ∧ p4) → ((p4 → (p4 ∨ (p5 → True))) ∧ p2))) ∧ (p3 ∧ p3)) ∨ ((p4 ∨ p1) ∨ (p5 ∧ True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648431243098072146157582300156 : (((((((False ∨ (((False ∨ ((p1 ∧ p2) ∧ False)) ∧ (p1 → ((False ∨ True) ∧ (False ∨ p3)))) ∧ True)) → False) → False) ∨ True) ∧ (p1 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804334276415461962519832328293 : (((p3 → ((((True ∨ True) → ((False ∨ (p4 ∨ (True → p4))) ∨ p3)) ∧ True) ∨ ((True → p2) → (((p4 → p3) ∨ p3) ∧ (p3 ∧ p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182081031314769791490021460143 : (((p1 ∧ ((((p3 ∨ p3) ∨ False) ∨ p2) → (False ∨ p5))) ∨ True) ∧ (((((False ∧ p2) → p4) → p5) ∨ p2) ∨ ((False ∧ (p5 ∧ p4)) → p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741490341346640348412711321469 : ((((p5 ∨ p2) ∨ (p5 → (p4 ∨ ((False → True) → (((((p4 ∨ (p4 ∨ p3)) → p5) ∨ p1) ∧ (p4 ∨ p1)) ∨ (p5 ∨ (p5 → True))))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617755756896914733386933963515 : (((((False ∨ (p5 ∧ (p1 ∨ (True → p3)))) ∨ (p3 → ((((p5 → p3) → (p5 ∧ p1)) ∧ False) ∨ (p3 → ((False ∨ p3) ∨ False))))) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196654050862636166250292371786 : ((((((p2 ∧ p5) ∨ p3) → True) ∧ p3) ∧ p2) ∨ ((((True → ((p2 ∨ p5) → p2)) → p2) ∧ (p1 ∨ ((p4 ∨ False) → False))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91253653325484156310120707077 : (((False ∧ p3) ∨ ((p2 ∨ p1) ∧ ((((p4 ∧ p3) ∧ ((p2 → (p3 ∧ (False → (p3 ∨ p3)))) → ((False ∧ False) ∧ p3))) ∨ p2) → p1))) → p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (((p4 ∧ p3) ∧ ((p2 → (p3 ∧ (False → (p3 ∨ p3)))) → ((False ∧ False) ∧ p3))) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353988970308299115416214157378 : (p4 → (p3 → (((p4 ∧ p5) → p5) → ((True ∧ ((p1 → ((p1 ∧ ((p1 ∧ (p1 → p2)) → p5)) ∧ ((p5 ∨ p5) ∨ p4))) ∨ p1)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16969253657196455093900877827 : (((p5 ∨ ((p3 ∧ (p3 → (((False ∧ (p3 ∧ p3)) ∧ (p5 ∧ ((p2 ∧ p1) ∧ p4))) → (p4 → p1)))) → p4)) ∨ (p1 → (p2 → p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150827925069767344710227115546 : (((((((p5 ∨ True) → True) ∧ (p2 → p2)) ∨ ((False ∧ (True → True)) → False)) ∨ (p3 ∧ (p2 → True))) ∨ p3) → (((True → False) ∨ p3) → p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h6.left
          let h8 := h6.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h9 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h10 := h3 h9
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h13 := h3 h12
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96465029371356245802754258339 : ((False ∨ (((p4 ∨ ((p4 ∧ p1) → p5)) ∨ (False ∨ p4)) ∧ ((True → False) ∧ (p1 → (True ∧ ((p1 → (p3 ∧ (False → p2))) ∨ True)))))) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h5.left
        let h14 := h5.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h15
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h5.left
        let h21 := h5.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h23 := h20 h22
        -- False on the left can always be used.
        apply False.elim h23



