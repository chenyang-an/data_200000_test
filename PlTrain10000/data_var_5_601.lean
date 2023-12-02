variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683905904348088692990287318184 : (((((p5 → (((p4 → (p3 ∨ False)) ∧ (True → ((p3 ∨ (p2 → False)) ∨ p1))) ∨ True)) ∨ False) ∨ (((True ∧ (True ∧ p2)) ∧ False) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_713637048523563831031452424015 : ((((((True ∨ p2) ∧ (True → True)) ∧ p3) → ((p1 ∧ ((p2 ∨ (p2 → p2)) → ((False ∨ p2) ∧ ((p5 → p4) → p1)))) → (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47277549678151172885838404554 : (((((True → (p4 → p4)) → p5) ∨ (p3 ∧ ((((False → (((False → p3) → p3) ∧ p1)) ∧ (False → True)) ∨ False) → p3))) ∨ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55218671867071343850240060298 : (((((False → p1) → p3) ∨ (p2 ∧ False)) ∨ ((p2 ∧ (p1 ∧ p3)) ∧ ((p4 → (True ∨ (True ∧ (p5 ∧ (p3 ∨ p4))))) → (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42726702772654973042587113048 : (((True → (((p1 → ((p3 → ((False ∧ p1) ∧ (p3 ∧ p1))) ∨ ((p1 ∧ (False → p3)) ∧ (p4 ∧ False)))) ∧ (p1 ∧ p5)) ∨ True)) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53028730703119446587598666800 : (((((p4 ∧ p5) ∨ p3) ∧ ((p2 ∨ (p4 ∧ p5)) → (p2 ∧ p2))) ∧ ((p5 → False) → (((p1 ∧ (True → p1)) ∧ p1) ∨ (p5 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173658181948983916804135763192 : (((((p5 ∨ True) ∨ (p3 ∧ ((True ∨ ((True ∧ True) → p5)) ∧ p3))) ∧ p4) ∨ p3) → ((p1 → True) ∧ (p2 ∨ (((True → False) → p2) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h10 := h8 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h23 := h21 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h25
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h29
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351522563954458457652360707476 : (p4 → ((((True → (p5 ∧ (((False ∧ p3) ∨ (True ∧ p3)) ∨ (p3 → (False ∨ p3))))) ∧ p5) → p2) ∨ (p3 → (True ∨ (p1 ∧ (p1 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311950700758942866675615505767 : (p2 ∨ (p3 ∨ (((p4 ∧ True) → (((p1 ∧ True) ∨ p3) ∨ False)) → (p3 → (((p4 ∨ (p5 → ((p2 ∧ p2) ∧ p2))) ∨ (p1 → True)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719925980833758281474623909282 : ((((p5 → ((True ∧ p5) → p3)) ∨ (p3 → (((((True ∨ False) ∨ ((True → p2) → p2)) → ((p4 ∧ p3) ∨ p2)) ∧ p4) ∨ (p2 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136376390291927705203699282108 : ((((p5 ∨ (p5 → True)) → p5) ∨ (((p1 ∧ (False ∧ (p5 ∨ ((p4 ∨ p3) ∨ (p4 ∨ p4))))) ∨ p5) ∨ (p3 → True))) ∨ (p3 ∨ (p2 ∧ p2))) := by
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
theorem thm_5_vars_310800497381111369399787390397 : (p2 ∨ ((p1 ∧ (p4 ∨ p5)) ∨ (True ∧ (p3 → ((((True → ((p5 ∧ False) ∧ (p2 ∨ False))) ∧ (p2 ∨ True)) ∧ (True ∨ (p2 → p4))) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h4
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h24 := h5 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619611155549711610909316579810 : (((((p1 ∧ p4) ∧ (((False ∧ p1) ∨ p4) ∧ (False ∨ (False → (p1 ∨ (p5 ∨ (p4 → ((p3 → ((False ∨ p4) → True)) → p3)))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_779698717764014705673308005021 : (((p2 ∨ (((((p2 ∨ False) ∨ p1) ∧ (((p1 ∨ (True ∧ p2)) ∨ (p2 ∨ (((p5 ∧ p3) ∨ p2) ∨ p1))) ∨ (p3 → p1))) → p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166757759382611601034595526550 : ((p4 → (p1 ∨ (p2 ∨ ((False ∨ ((True ∧ p3) → (((p2 ∧ p1) ∨ p2) ∨ True))) ∨ p2)))) ∨ (p2 ∧ ((p2 → (True ∨ (p2 ∧ p3))) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121312674841100567228336979809 : (((((True ∨ (((((p3 → True) → (True → True)) → p5) → True) ∨ p3)) → ((p1 ∨ (p2 → p4)) ∧ (p2 ∨ True))) ∧ p1) → p4) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133580020648520000337997448000 : ((((((False → p3) → p1) ∨ ((p4 ∧ (p5 ∧ ((p3 ∧ p2) ∨ (p2 ∨ ((p3 ∧ p2) ∨ p4))))) ∧ False)) ∨ p5) ∧ p3) ∨ (p2 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304775301220197487322917268774 : (p1 ∨ ((p3 ∨ (((((p3 ∧ (True → p3)) → p2) ∨ (((p5 ∧ (p4 → p2)) → p4) ∨ (p5 ∧ True))) → p4) ∨ (p4 ∨ p3))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187778645599853952198734731574 : ((p3 → (((p1 → True) → (p5 ∧ (False → (p2 ∧ p4)))) ∨ p4)) → (((True → (p4 → p5)) ∨ True) ∨ ((p5 ∧ ((p2 ∧ p5) → p5)) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48931472309163980932904443403 : ((((((p1 ∧ (p2 → p2)) → ((True → (False ∨ ((p3 ∧ (p5 ∨ p4)) ∧ False))) ∧ p4)) → (True ∧ p1)) ∧ p1) ∨ (p1 ∨ (True ∨ p5))) ∨ p5) := by
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
theorem thm_5_vars_1528485523149867824602645828 : (((p4 ∨ (False ∨ False)) ∨ (True ∧ (((((p4 ∨ p1) ∧ ((p4 ∨ (p2 → True)) → (p5 → True))) ∨ p1) ∨ p4) ∨ False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354836232213550738457980369237 : (p5 → (((False ∨ p4) ∧ (((False → p2) → ((True ∨ ((p5 ∧ (True → (True ∨ (p2 ∨ (p2 ∨ (False → p4)))))) ∨ False)) ∨ p1)) → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66497450661700106641208703290 : ((True → (((p5 ∧ p3) ∨ ((((False ∨ (p2 → p4)) ∧ ((p1 ∨ ((False → (p3 → p4)) → p5)) ∨ p1)) ∧ True) ∧ (False ∧ True))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112728326670742120274792854250 : ((((((p2 ∧ p2) → (((p1 → p5) ∨ p2) → p2)) ∨ ((p4 ∨ False) ∧ p3)) → (((p3 ∨ p4) ∧ True) → (p2 ∧ p3))) → False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301145500322822027476108341013 : (False ∨ (((False ∧ ((p5 ∨ p1) ∧ False)) ∧ (p3 ∧ p1)) ∨ ((False ∧ p5) → (((((p5 ∨ False) ∧ True) ∧ (p5 ∧ p1)) ∨ (p5 ∧ False)) → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115098326319369935861275253594 : (((((p1 ∧ ((p4 ∨ p2) ∨ ((p1 ∧ False) ∨ p2))) → False) ∧ p4) → (True ∧ (((p1 ∧ p1) ∨ p5) ∨ ((p3 ∧ p5) ∨ True)))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_114943648975345779585614146809 : ((((p1 ∧ (False ∧ p5)) → ((p5 ∧ p5) → (p3 → (p4 ∨ (p3 → True))))) → (((p5 → (p5 ∨ p4)) ∧ True) ∧ (p3 ∧ p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64929976395465697232671188468 : ((p2 ∨ ((((p5 ∨ False) ∨ (p3 → p4)) → ((p4 ∨ p2) → ((True → p5) → p5))) ∨ ((p2 ∨ (p5 ∨ p3)) ∧ (p3 ∨ (p2 ∧ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57922985862616698277397792168 : (((p5 ∨ (p5 → p5)) → (((p3 ∨ ((((p3 ∧ p4) ∧ False) ∧ ((p2 → p1) ∨ p2)) ∨ ((True → p5) → True))) → (False ∧ p2)) → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ ((((p3 ∧ p4) ∧ False) ∧ ((p2 → p1) ∨ p2)) ∨ ((True → p5) → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ ((((p3 ∧ p4) ∧ False) ∧ ((p2 → p1) ∨ p2)) ∨ ((True → p5) → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208959711494567213812988432370 : ((True ∨ ((False → (p3 ∨ p1)) → False)) → (((p3 ∧ (p4 ∨ p4)) ∧ (p4 ∧ ((p1 ∧ True) → ((False → ((p5 ∨ p3) → True)) ∨ True)))) ∨ True)) := by
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
theorem thm_5_vars_137888667072850709783093413990 : ((p4 ∨ ((((((((True → (p1 ∨ False)) ∧ p5) ∧ p5) ∨ p3) ∧ ((p4 → p2) ∧ True)) ∨ p5) ∧ (p1 ∧ p1)) → p4)) ∨ ((p3 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51359328482942956347401349580 : ((((((True ∧ (p1 ∧ p1)) → p4) ∧ ((((True ∧ True) ∨ (p2 ∨ True)) ∧ p2) ∧ p2)) ∧ p4) → ((p5 ∧ (False ∧ True)) ∨ (p4 → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143983181778654597553241287402 : ((((p4 ∧ p3) → (((p3 ∧ p2) ∨ (p1 ∨ (p1 ∨ (p1 ∧ ((p1 → (p2 ∨ p5)) → p5))))) ∨ p4)) ∨ p3) ∧ ((p5 ∧ (False ∨ False)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192220351279338852746927971130 : ((((p5 ∨ (((False ∧ p2) ∨ p1) → p1)) → p5) ∧ p4) → ((((p1 ∨ True) ∨ p3) → ((p2 ∧ (p3 → (p1 ∧ p4))) ∧ (p2 ∧ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (((False ∧ p2) ∨ p1) → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345536370323312839849884142668 : (p3 → ((((((p2 ∨ (p5 ∧ False)) ∧ p2) ∨ p4) ∧ p2) ∨ (((p5 ∨ p4) ∨ (((False ∧ (p1 → p1)) ∨ p3) → p1)) ∨ (p1 ∧ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184656043255274246957507477373 : (((((p5 → True) ∧ (p3 → p3)) → p1) ∨ ((p5 ∨ False) → p5)) ∨ ((p3 ∧ ((((False ∨ (p2 ∧ (True ∨ False))) ∨ p4) → True) ∧ p2)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714349210316487001730933040799 : (((((p1 ∨ (p1 ∨ p5)) ∨ (True → p3)) → ((False → p4) ∧ ((False ∨ p4) ∧ ((((p1 ∨ p1) ∧ p3) ∨ (p2 → (p3 → p1))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58118346030065140829648796864 : (((p2 ∧ True) ∧ (((((p1 → False) ∨ (((((False ∧ p4) → False) ∨ (p2 ∨ p1)) → True) ∨ (p4 → p2))) → (p3 ∧ p4)) ∨ p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53186245052923949212527043789 : ((((p2 → (p4 → ((p2 → True) ∧ ((p1 ∧ True) → p1)))) → p3) ∨ (((False ∧ True) → ((p2 ∧ True) ∨ ((p3 ∧ p1) ∨ p3))) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738359369190754432035256647522 : ((((p1 ∧ False) ∨ (((((((p5 ∨ False) ∧ (p2 ∨ p4)) ∨ p2) ∧ (p3 → p5)) ∨ p2) ∧ p2) → (False ∨ ((p5 ∧ (p4 → p1)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148235169742708719955123642163 : ((((p5 ∧ ((True ∨ (((p4 ∧ False) ∨ (p2 ∨ p3)) ∧ p1)) → p2)) ∨ (p3 → p5)) ∨ (True → (p5 → p2))) ∨ ((p3 ∧ (p5 ∧ True)) → p3)) := by
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
theorem thm_5_vars_174259792790097953659545427172 : ((((((p4 ∧ p4) ∨ True) ∨ (p1 ∧ (p5 → p1))) ∨ p1) ∧ ((True ∧ p2) ∧ p3)) → ((((p2 ∧ (p3 → p5)) ∨ (p2 ∧ p3)) ∧ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h3.left
        let h10 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h12
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h17
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h24
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h3.left
    let h27 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h29
    -- One of the premise coincides with the conclusion.
    exact h27
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h31.left
        let h38 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h39 := h37.left
        let h40 := h37.right
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h31.left
        let h43 := h31.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h42.left
        let h45 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h45
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h31.left
      let h50 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h51 := h49.left
      let h52 := h49.right
      -- One of the premise coincides with the conclusion.
      exact h52
  case inr h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h31.left
    let h55 := h31.right
    -- Conjunctions on the left can always be decomposed.
    let h56 := h54.left
    let h57 := h54.right
    -- One of the premise coincides with the conclusion.
    exact h57
  -- Conjunctions on the left can always be decomposed.
  let h58 := h1.left
  let h59 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h58
  case inl h60 =>
    -- Disjunctions on the left can always be decomposed.
    cases h60
    case inl h61 =>
      -- Disjunctions on the left can always be decomposed.
      cases h61
      case inl h62 =>
        -- Conjunctions on the left can always be decomposed.
        let h63 := h62.left
        let h64 := h62.right
        -- Conjunctions on the left can always be decomposed.
        let h65 := h59.left
        let h66 := h59.right
        -- Conjunctions on the left can always be decomposed.
        let h67 := h65.left
        let h68 := h65.right
        -- One of the premise coincides with the conclusion.
        exact h68
      case inr h69 =>
        -- Conjunctions on the left can always be decomposed.
        let h70 := h59.left
        let h71 := h59.right
        -- Conjunctions on the left can always be decomposed.
        let h72 := h70.left
        let h73 := h70.right
        -- One of the premise coincides with the conclusion.
        exact h73
    case inr h74 =>
      -- Conjunctions on the left can always be decomposed.
      let h75 := h74.left
      let h76 := h74.right
      -- Conjunctions on the left can always be decomposed.
      let h77 := h59.left
      let h78 := h59.right
      -- Conjunctions on the left can always be decomposed.
      let h79 := h77.left
      let h80 := h77.right
      -- One of the premise coincides with the conclusion.
      exact h80
  case inr h81 =>
    -- Conjunctions on the left can always be decomposed.
    let h82 := h59.left
    let h83 := h59.right
    -- Conjunctions on the left can always be decomposed.
    let h84 := h82.left
    let h85 := h82.right
    -- One of the premise coincides with the conclusion.
    exact h85



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302799750924243687185158604223 : (False ∨ (p5 ∨ (((False ∧ ((p4 → ((((p4 ∧ p1) ∧ p5) ∧ True) → (p5 → (p4 → p4)))) ∧ ((p4 → (p5 ∨ p2)) ∧ p3))) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714322585534465328059865355990 : ((((((p2 ∨ p5) → p3) ∨ (p2 → p5)) → (((False ∨ p3) ∧ ((False → (p4 ∧ (False → p5))) → ((p1 ∨ p5) → p1))) ∨ (p2 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323185230924471747532398902106 : (p5 ∨ (((p3 ∨ ((((False ∨ p2) ∨ ((((p3 ∨ p2) ∨ False) ∨ True) ∧ (p2 ∨ True))) ∨ ((p5 → True) → p1)) ∨ True)) ∨ p3) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165009169692569870470532241925 : ((((p1 ∧ (p2 ∨ (p1 → (p2 ∧ p2)))) ∨ (p4 → ((p4 ∧ (p3 → p2)) ∨ True))) → False) ∨ (((p1 ∧ ((True ∧ p3) → True)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156905885624753680290270290742 : (((((False → (False ∧ (p5 ∧ ((False ∨ ((False ∨ (True ∨ p2)) → True)) ∨ p1)))) ∧ True) → p2) ∨ p5) ∨ ((p4 → (False ∧ p3)) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114225095674123372736485779928 : (((True ∧ (((p2 → ((((p5 → False) ∧ p4) ∨ p4) ∧ (((p5 ∧ p3) ∧ False) ∧ p1))) ∨ False) ∧ p2)) → ((p5 ∧ p3) ∧ p5)) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h26.left
  let h28 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h28
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172028371167464553298606812221 : ((((True → p3) → (((p3 ∧ (True ∧ p2)) ∨ p5) ∧ (p5 ∧ p5))) ∨ (True → p5)) ∨ ((True ∨ p3) ∨ (p3 → (p4 → (p1 → (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113750644994630673700072951952 : (((((((p3 ∧ (p3 → p3)) → (p4 ∨ p2)) → p3) → p3) ∨ ((((p2 → p1) ∧ p1) → (p3 → p2)) ∧ p1)) → (p1 → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231035270098728686329227576649 : (((True ∨ True) ∨ p2) → (((False → True) ∨ p5) ∧ ((((p3 ∧ p5) ∧ (p2 ∨ ((False ∧ p4) ∨ p5))) ∨ True) ∨ ((p5 ∨ p2) ∨ (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185156686120935446080968066483 : (((p3 ∨ p5) → (((p3 → False) ∧ p2) → (False ∧ (p5 → p2)))) ∨ (((p5 ∨ False) ∨ (False → (True ∨ ((False ∨ (False ∧ p2)) ∧ p5)))) ∨ p3)) := by
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
theorem thm_5_vars_118568363818038060923142706049 : ((p4 ∨ ((True ∧ (p4 ∧ (((p2 ∨ p1) → ((False ∧ True) ∧ ((True ∧ (p1 ∨ (p2 → (False ∧ p3)))) → p5))) ∨ p4))) ∧ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265789774957493925019403747316 : (True ∧ (p4 ∨ ((p4 ∨ p4) ∨ (((p1 → ((False ∨ p5) ∧ ((p4 ∨ p5) → p1))) → ((p1 ∨ (p2 ∧ p2)) ∧ ((p3 ∧ p2) ∨ False))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303945368414283325384579905126 : (p1 ∨ (((p1 ∨ ((p4 ∧ (p5 ∨ True)) → p2)) → (((p5 ∧ (((p1 → True) → True) ∧ p2)) ∨ (p2 ∧ ((p3 → True) ∨ p4))) → p2)) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312470908476691332118629002179 : (p2 ∨ (p5 → ((((p3 ∨ p2) ∧ ((p2 ∨ True) → (((p1 → (((p5 ∧ p4) ∧ ((False ∧ False) → p2)) ∨ True)) ∧ p3) ∧ p5))) ∨ p5) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42835635699211673095455357782 : (((p1 → (p4 ∨ ((p4 → p3) → (False ∧ (p2 ∧ (p4 ∧ (True → (p2 ∨ ((True → (((p4 → True) → p2) ∨ True)) ∧ p1))))))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251843992781392447242751603183 : ((p3 → p5) ∨ ((p4 ∨ (((((((p1 ∨ p2) ∧ True) ∧ ((p4 ∧ p3) → (True → (True ∧ False)))) → (p2 → False)) → p4) → p4) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192828252610060121299914840731 : (((p5 → ((p4 → True) → (p1 ∨ (p2 → p5)))) → p4) → (p5 ∨ ((p3 → p2) → ((True → (p4 → ((p5 ∧ p3) ∧ p4))) ∨ (True ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355926100446974999239162647839 : (p5 → ((((p2 ∨ False) → (((p2 ∧ p3) → (p2 → True)) → p5)) ∧ (((p2 ∧ False) ∨ (True ∨ p4)) → (p2 ∧ False))) → ((p4 ∧ p1) ∧ True))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∧ False) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 ∧ False) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194730838964809586822052419575 : (((p1 ∧ ((p1 ∨ p2) ∧ (False ∧ p2))) ∨ True) ∧ (((p1 → ((((p3 ∧ (p2 ∨ p2)) ∨ p3) ∨ False) ∨ (p2 ∧ False))) ∧ (True ∨ p4)) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258538330660355068483303835769 : ((p5 ∨ p3) → (((p5 ∧ (p5 ∨ True)) ∨ (p3 ∨ ((((p1 ∧ p5) ∨ p2) → ((True → True) ∧ False)) ∧ p3))) ∧ ((p4 ∨ p4) ∨ (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225122010751040538829472510043 : (((p2 ∧ p4) ∧ p5) ∨ ((((p4 → ((p4 → p2) ∧ (p1 → (((p3 ∧ p4) ∨ p4) → p5)))) → p5) ∧ p1) ∨ (True ∧ ((False ∧ p5) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49502412127672818791388460234 : ((((False ∨ (p5 ∨ (False → (p4 ∧ ((p5 → (False ∧ ((p3 ∧ False) ∧ ((p4 → True) → p2)))) ∨ p1))))) → p2) → ((p4 ∧ p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636859783914870720447431944539 : ((((((p5 ∧ True) ∧ (((True ∨ (((p4 ∧ False) ∨ p2) ∧ False)) → False) ∧ p1)) → (False → ((((p3 ∧ p1) ∨ p1) → p1) ∨ p1))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350338700092279942662016411018 : (p4 → ((p2 → ((p2 ∧ ((True ∧ ((p3 ∨ p2) ∨ ((p5 ∨ False) ∧ (p3 ∨ True)))) → ((p4 → ((p4 → p3) → False)) ∧ True))) → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340238680133756649138212796645 : (p1 → (p5 → (((p1 ∨ (p5 ∨ False)) ∨ p2) → (((p5 ∧ (True ∧ p3)) ∧ (p1 ∧ (p5 ∨ True))) ∨ (True → (p2 → (True ∧ (p3 ∨ True)))))))) := by
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
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148157290507870743663766895623 : (((p2 → ((p3 → ((False ∧ (((((False → p1) ∨ True) → p3) → p4) ∨ p2)) ∨ True)) ∧ p2)) → (p2 ∧ False)) ∨ ((p5 ∨ (True ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4644851420264229001389745288 : (p5 → (((p2 ∨ (p2 ∨ p3)) ∨ (p2 ∧ ((((False ∨ ((p3 → True) ∨ p5)) → (True ∨ (False ∧ p4))) ∧ p1) ∨ p5))) → (p4 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261670950414671616684898981949 : ((p5 → p5) → (p5 → (((p1 ∧ p4) ∨ (p4 ∨ ((p2 ∧ ((p1 → (((False ∨ (p1 → p4)) → (p3 ∨ p3)) → p4)) ∨ p1)) ∨ p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55927973887969639849653037008 : (((p1 → ((p5 ∨ p2) ∨ p1)) ∧ ((((((p2 ∨ p2) → (True ∧ ((False → False) → (p3 ∨ p2)))) ∨ False) ∧ (p5 ∧ p2)) ∨ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247338123355370340543207295425 : ((False ∨ False) ∨ (p4 → (((((p1 ∧ p4) ∧ (p2 ∧ True)) ∧ p1) ∨ ((True ∧ ((p4 ∧ True) ∨ p4)) ∧ (False → p1))) ∨ (p5 ∧ (p4 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252158304591024194127663104287 : ((p4 → p3) ∨ ((p3 ∧ ((p3 ∨ (p1 ∧ ((p2 → ((p4 ∨ ((p3 ∧ (p4 ∨ p2)) → (p4 → p1))) ∨ p5)) → True))) ∨ p3)) → (p5 → p3))) := by
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662350203776918610414747006595 : (((((p5 ∨ ((False → (False ∨ (p5 ∨ p4))) → p5)) ∧ (((p2 ∨ p3) → ((p3 ∧ (p4 → p4)) → (p5 ∧ p4))) → p4)) → (p1 → p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (False → (False ∨ (p5 ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53488957126256387757619934966 : (((p5 ∧ (((p5 → p3) → ((True ∧ (True ∧ p4)) ∧ p5)) ∧ p4)) → ((p5 → p2) → (p3 → ((p3 ∧ p1) ∧ (True ∨ (False ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150218391773138547204530913981 : ((p2 → ((p2 ∨ True) → ((p4 ∨ ((False ∨ ((p2 ∧ (p1 → p5)) → p5)) ∧ p3)) ∨ ((p5 ∧ p5) ∨ p3)))) ∨ (((p1 → p5) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174378947693813896339653336311 : (((((False ∨ p5) → (p1 ∨ (True ∨ p3))) → False) ∧ (p5 → ((p1 ∨ p5) ∨ False))) → ((p5 ∧ p4) ∨ (False ∧ (((False ∧ True) → p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ p5) → (p1 ∨ (True ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156965474933221749993879883591 : (((((p2 ∧ (False ∨ (p1 ∨ ((p2 ∧ True) ∨ False)))) → p3) ∧ (((p4 ∧ False) ∨ p2) ∨ p5)) ∨ False) ∨ (p5 ∨ (((p4 ∧ p2) → p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207474384431740477628618629720 : (((p1 → ((p4 ∨ p3) → True)) ∨ p2) → ((p1 ∨ p3) ∨ (False ∨ (((False ∧ p5) → (((p1 ∨ (False ∧ p2)) → (p2 ∧ False)) → p4)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210768343811725124570752371226 : (((False ∧ (True ∨ p5)) → p2) ∧ ((((p2 ∨ (((p3 ∨ p2) → p5) ∧ p2)) ∧ (p5 ∨ (p5 → p3))) → False) → (p2 ∨ (True ∨ (True ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64501952537536532709508911891 : ((p1 ∨ (((p3 ∨ p2) ∧ ((p2 ∧ p3) → (p5 → ((p5 → True) ∨ (True ∨ False))))) ∧ (((p4 ∨ (p3 ∨ (p2 ∨ p4))) ∧ False) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252507266933319594232611685369 : ((p5 → p2) ∨ ((((False ∨ ((False → p1) → (p4 ∨ ((p2 → True) ∧ (False ∧ (p1 → (False → p3))))))) ∧ (p1 ∧ (False ∨ True))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644125564354689358248463614633 : ((((True ∨ (p1 ∧ (((((p4 ∧ p1) → (p4 → ((p3 → True) → (p5 ∧ False)))) → False) ∨ p1) ∧ (((p5 → True) ∨ p4) ∨ p2)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310221494107234115790406454304 : (p2 ∨ ((p4 ∧ (((False → ((p2 ∨ p3) ∨ (p2 → p3))) ∨ p2) → p2)) ∨ (((((True ∧ True) ∨ p5) ∧ (p5 → (False ∧ False))) ∧ False) → p4))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43619356959582838330647740437 : (((((p1 ∧ (False ∨ (((((((p3 ∨ True) ∨ True) ∧ (p4 ∧ p4)) → p3) ∨ p1) ∧ p3) → ((p5 → p1) → p3)))) → p5) → p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336265372787164636866664242566 : (p1 → (((p2 ∨ (((((p4 ∧ p5) → (p2 → p1)) ∧ (p2 ∨ p2)) ∨ p3) → False)) ∨ ((p4 ∨ True) ∧ (True → (p4 ∧ (p3 ∧ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136033699204821835826376650432 : ((((p5 ∨ True) ∨ (p4 ∨ (((p4 → p1) → False) ∧ p1))) → (((p2 ∨ p3) ∧ ((p5 → True) → (False ∨ False))) → p3)) ∨ ((False ∧ p1) → False)) := by
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
theorem thm_5_vars_707927150543426903352816256907 : ((((p5 ∧ ((p5 ∨ p1) ∨ (True ∧ (p3 → p1)))) ∨ (((False ∨ (True ∨ True)) ∧ p3) ∧ (p2 → (p3 ∨ ((False → (p5 ∧ p1)) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150249768891582016258182520818 : ((p3 → (((True → (((p4 → p4) → p4) ∨ ((p1 ∧ p1) → (False ∧ p2)))) ∨ p3) ∧ ((p5 ∧ p5) ∨ p3))) ∨ (p2 → (p3 ∨ (p1 → p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301234778527786760492963701903 : (False ∨ ((p3 → (p2 ∨ (True ∨ (False → True)))) ∧ (((p2 ∧ (False → ((False ∧ True) ∧ (p2 → p1)))) → (((False ∨ p3) ∨ p4) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324489498279702720268452942069 : (p5 ∨ (((True ∨ (True ∧ False)) → p2) ∨ ((p5 → (p4 ∨ (((((False ∧ p3) ∧ p4) ∨ (((p2 ∨ p5) ∧ True) ∨ p3)) ∨ p4) ∨ p3))) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682900751028411948526758533500 : (((((p5 ∨ True) ∧ ((p3 → (p1 ∧ ((((p2 → True) ∧ p1) ∧ (p3 → p3)) ∨ False))) → p4)) ∧ ((p4 ∧ (True → p2)) → (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733919275985657682050232341085 : ((((True ∨ True) ∧ ((p1 ∨ p4) ∧ (((p3 ∧ p3) ∨ ((False ∧ False) → p4)) ∧ ((((False → (False ∨ (True ∨ p1))) ∧ True) → p2) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84734066068675813006695673271 : (((((((p3 → False) ∨ (p2 → True)) ∨ p4) → False) ∧ (p2 ∨ (True ∧ False))) ∧ (((p5 ∧ p2) ∨ (p3 ∨ (p5 → False))) ∧ (p5 ∨ p2))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : (((p3 → False) ∨ (p2 → True)) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h20 := h4 h18
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : (((p3 → False) ∨ (p2 → True)) ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h26 := h4 h24
          -- False on the left can always be used.
          apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225026340822167648349187393484 : (((False ∧ p1) ∧ p5) ∨ (((((p3 → True) ∨ True) → (p3 ∧ (p4 ∧ p5))) → (((p3 ∨ p5) ∨ p1) ∨ ((True ∨ p2) ∧ p2))) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249110047258965838941177654812 : ((p4 ∨ p2) ∨ (((p4 ∨ p2) ∨ ((p2 ∨ (p4 → ((p4 → p4) ∧ ((((False ∨ (False ∨ p4)) ∧ True) → False) ∨ True)))) ∨ (p4 ∨ p5))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138044318708765386587678016743 : ((True → (((p4 ∧ (p1 ∨ p3)) ∨ p4) ∨ (((p1 ∧ (True ∨ p5)) ∨ (p4 ∧ (True → (p5 ∧ (True ∨ False))))) ∨ True))) ∨ (p1 ∨ (p4 ∧ True))) := by
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
theorem thm_5_vars_251530862581808175437064868210 : ((p3 → False) ∨ ((((p1 ∨ ((((p3 → p2) ∧ p2) → ((p4 → p3) ∨ ((False → ((p3 ∨ p5) ∨ p4)) ∨ True))) → False)) ∧ p4) → p1) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p3 → p2) ∧ p2) → ((p4 → p3) ∨ ((False → ((p3 ∨ p5) ∨ p4)) ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h6
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340975909375869671881450513981 : (p2 → (((p3 ∧ p2) ∨ (p4 ∨ (((p2 ∨ ((p3 → True) ∧ (p2 ∧ (((p2 → p2) → p4) → (p1 → p4))))) → (p3 ∧ p3)) ∧ p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40335502141738127838429330084 : ((((((p4 ∧ ((p1 → p3) → (True ∧ (p1 → (p4 ∧ p2))))) ∨ ((p5 → ((p1 → p3) ∧ False)) ∨ (p2 ∨ True))) ∨ True) ∨ p3) ∨ p3) ∨ p4) := by
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



