variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624872423472399187652249542895 : ((((p5 ∨ ((((p2 ∧ (True ∧ p3)) → False) ∨ (p2 ∨ (True → (p4 → p3)))) ∨ ((p4 ∨ ((p3 ∨ p3) ∧ p5)) → (p4 ∨ p5)))) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305767674794280515594254579829 : (p1 ∨ (((p4 → (p3 ∨ ((True ∧ p4) ∨ p5))) → p4) ∨ (p5 → (((p2 ∨ p1) ∧ ((((p4 → True) ∨ True) ∧ (p1 ∧ p4)) ∧ p5)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h20.left
      let h26 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633554805324915381918844793337 : ((((((p2 ∧ (((True ∧ True) ∨ p2) ∧ (p1 ∨ p1))) → ((p3 ∨ (((p3 ∧ False) → (p1 → p3)) → True)) ∧ p5)) ∨ (p4 ∧ False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168188128811146611439282784539 : ((((False ∧ p1) ∧ False) ∨ ((((False ∨ p2) ∨ ((p1 ∧ p2) ∨ True)) → (False ∧ False)) ∧ p3)) → (p5 ∨ (((p4 ∧ (p5 → p5)) ∧ p3) → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : ((False ∨ p2) ∨ ((p1 ∧ p2) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114417721059202951522400878340 : ((((p4 ∧ p5) ∨ ((p1 → False) ∧ (p3 ∨ (p3 ∧ (((p3 ∨ p1) ∨ (True → p3)) → p1))))) ∨ (False → (p5 ∧ (False ∧ True)))) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63905890326763504462497808572 : ((False ∨ (((True ∨ (p1 → p3)) → (((p4 ∧ ((True ∨ (p2 ∨ (p1 → (False ∧ p3)))) ∨ True)) ∨ ((False ∨ p1) ∧ False)) → False)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180017109302471780676197410993 : ((((False → p1) → (p1 ∨ (((False ∨ False) → (p3 ∧ True)) ∨ p2))) ∨ True) → (p3 → (((True → p5) → (False → False)) ∧ (p1 → (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171539250633268262856341695474 : ((((p3 ∧ (((p5 → p2) ∧ p1) ∨ (((p1 → False) → p3) ∨ p1))) ∨ True) ∨ p4) ∨ (((p2 ∨ (p5 ∧ p1)) ∧ (p4 → p3)) ∧ (False ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300069941275857995568780470409 : (False ∨ (((p2 ∨ (p3 ∧ (((False → (True → (((p2 ∧ (p5 ∧ (p5 → p5))) ∨ False) → p1))) → p2) ∨ (p3 ∨ p1)))) ∨ True) ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323904523192425222228845846578 : (p5 ∨ (((p3 ∨ p1) ∧ (p3 ∧ (p5 ∧ ((p1 ∨ ((True ∧ p4) ∧ (True → p5))) ∧ True)))) ∨ (((p1 ∨ p5) → True) ∨ ((p5 ∨ False) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111872432813250213071216676118 : ((((p1 ∧ (p3 → ((p4 ∨ (p3 ∧ ((p5 ∧ p3) ∨ (p2 ∨ (p2 ∨ p4))))) ∧ p1))) ∨ (p1 ∨ (p2 → (p1 ∧ True)))) ∨ True) ∨ (False → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254297055144273713951312999900 : ((p2 ∧ p3) → ((False ∨ (((p4 ∨ p2) → False) ∨ False)) → ((((p4 → (p1 → p2)) ∧ ((p3 → (p3 ∧ p3)) ∨ (p2 → False))) → p4) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : (p4 ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h1.left
        let h20 := h1.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h21 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h22 := h15 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h24 =>
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h1.left
      let h28 := h1.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h29 : (p4 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h30 := h26 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- False on the left can always be used.
      apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215822905559142103853103384193 : ((p2 ∨ ((p5 → p5) ∧ False)) ∨ ((((p2 ∨ (((True ∨ True) ∧ False) → True)) ∨ ((True ∧ (False → True)) ∧ True)) → (True ∧ False)) → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (((True ∨ True) ∧ False) → True)) ∨ ((True ∧ (False → True)) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44759261104914624762482869342 : ((((((p1 → p3) → p4) ∨ p2) → (((p2 → ((p2 → (p3 ∨ p1)) ∧ p2)) → p2) ∨ ((p2 → p2) ∧ ((p1 ∧ p1) ∧ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191829931900637744133350438117 : ((p3 ∨ ((p2 ∨ (p1 → ((p5 ∧ p1) ∧ True))) ∨ p3)) ∨ ((p5 ∨ p3) ∨ (False ∨ ((((p3 → (p4 ∧ True)) ∧ p5) → (p5 ∨ p4)) ∨ False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346927023189386053394763268149 : (p3 → ((p1 → ((((p5 → p5) → ((p5 → p4) ∨ True)) ∨ False) → ((p5 → (p3 ∨ True)) → p4))) ∨ ((p5 ∨ True) ∨ (False ∧ (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117588476848703815303957180895 : ((p2 ∧ (p2 ∧ (False ∧ ((True ∨ (((True ∧ (p2 → True)) → p5) ∧ (p3 ∧ p2))) ∧ ((False ∧ p3) ∧ (p4 ∧ (False ∨ True))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184071578957512563303535980042 : ((((p5 ∨ (p1 → (True ∨ p3))) ∧ ((False ∧ p2) ∨ p5)) ∨ p4) ∨ (False ∨ (((False → (True ∧ ((p2 → p4) ∧ p1))) ∨ (p1 ∨ p1)) ∨ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763392660689035215258988599171 : (((p3 ∧ (True ∧ ((True ∧ (True ∧ (((p3 ∧ ((p1 → p3) ∨ ((p5 ∧ p4) ∨ True))) ∨ False) ∧ p3))) → (p5 ∨ ((p3 → p4) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168653415739255652649052833411 : ((p4 ∧ ((p2 → False) → (((p1 → p5) ∨ ((p1 ∧ ((p3 ∧ True) → p2)) ∨ True)) ∨ p1))) → (((True ∨ False) → p3) ∨ ((False → True) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248301857580975532000171350448 : ((p2 ∨ p2) ∨ (p1 ∨ (((p5 ∨ (False ∧ ((p4 ∧ (p2 ∨ p3)) → True))) ∧ p3) ∨ (((((False ∨ False) ∨ True) → p2) ∨ True) ∨ (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_45874989273461023666489393006 : (((p3 → (((True ∧ (((p2 → p2) ∧ p2) ∨ (p1 → False))) ∨ p2) → ((p1 ∨ ((False ∨ ((p5 → p5) ∨ False)) ∨ p3)) → p2))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179468650900473815105730596237 : ((True → (((((True → p1) ∨ (False ∨ p2)) ∨ p4) ∨ (False ∧ p5)) ∧ p5)) ∨ ((False ∨ (p5 ∧ p2)) → (((True ∧ p1) ∨ p2) → (p5 ∨ p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696133427096126953528286551384 : ((((False ∨ ((False ∨ (p5 ∨ ((True → False) ∧ (p3 → p5)))) ∧ (False ∨ p5))) → (((((p1 ∨ p3) → (p3 ∨ p1)) ∧ True) → True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180369557535659133007908805221 : ((((p4 → (((False ∨ p5) ∨ p5) ∧ (p4 → p1))) → p2) ∨ (p4 ∨ False)) → (p3 → ((p4 ∧ ((p2 ∧ (p4 → False)) ∧ (False → p1))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338786362884063310161792802657 : (p1 → ((p5 ∧ True) ∨ (p2 ∨ (((p2 → (p4 → ((((p3 → ((True → (True ∧ False)) ∧ p1)) → p4) → (p3 → p3)) ∧ False))) → p4) ∨ p1)))) := by
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
theorem thm_5_vars_111838183786413419018921587052 : ((((((p1 ∨ (p2 ∨ (True → p4))) → False) ∨ ((((p3 ∧ True) ∧ p5) ∧ (True ∧ p3)) ∨ p4)) ∨ ((True ∨ True) ∨ False)) ∨ p5) ∨ (p2 ∨ p2)) := by
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
theorem thm_5_vars_630486839493652720559343880853 : (((((False ∨ ((p5 ∨ False) → (False → (((((p2 ∨ (p2 ∧ (p3 → p3))) ∧ p3) ∧ (p5 → p2)) ∧ (p5 → True)) ∨ p4)))) ∨ p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174078569369697332117251153658 : ((((((True ∧ (p3 → p2)) ∧ ((p2 ∧ p2) ∧ p2)) ∨ True) → p5) ∧ (p3 → True)) → (((p4 → p3) → (p5 → (p4 ∨ p5))) ∨ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∧ (p3 → p2)) ∧ ((p2 ∧ p2) ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323998114249526701211730414356 : (p5 ∨ (((False ∧ p4) ∨ (True ∧ ((p5 ∧ (p2 → (True → p3))) → (p4 ∧ p1)))) ∨ (p2 → (False → (p4 → (((p5 ∧ p1) ∨ p3) ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738602995971449936854836614466 : ((((p2 ∧ True) ∨ ((p1 ∧ p5) ∧ ((False → p1) ∧ ((((p5 → (True ∨ (p2 ∧ p4))) → p1) → p5) ∨ ((p5 ∧ (p1 ∧ False)) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111140366042479580774202341043 : (((((p2 ∧ (p5 ∨ (p4 ∧ p2))) ∨ p3) ∧ (((True ∨ p1) → ((p3 → p3) ∧ ((p3 ∧ p3) ∧ p5))) ∨ (False ∨ p4))) ∧ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766776254468283083427368769769 : (((p4 ∧ (p2 ∨ (p4 ∧ ((p4 ∧ p5) ∧ (((((True ∨ p5) → p5) ∨ (p5 ∨ p2)) ∨ p1) ∨ ((p1 ∨ p2) ∨ ((p5 → p5) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56926282637472786504071687274 : (((True ∨ (p3 ∨ p4)) ∧ (((((p3 ∧ p5) ∨ ((p1 ∨ p4) → (False ∧ p4))) → p4) ∨ (True → (True ∧ p2))) → (p5 ∧ (False → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114963963082666037777019274592 : (((True → ((p2 → (p2 ∨ ((p5 → ((p4 ∧ p2) ∨ False)) ∧ False))) ∨ p1)) → ((p3 → ((p5 → False) ∨ p3)) ∨ (p2 → p1))) ∨ (p1 ∧ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323198679887016095343367668118 : (p5 ∨ ((((p3 ∨ ((((p2 ∧ (p1 ∧ p5)) → (p3 ∧ True)) ∨ p2) ∨ (p3 → (p1 ∧ p1)))) ∧ (p2 ∧ True)) ∧ (True → p3)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44359708337971128350023174490 : (((((True → (((p3 ∨ ((p5 ∧ p2) ∧ p3)) ∧ (p3 ∧ p3)) → False)) ∨ p4) ∧ ((p3 → ((False ∧ p5) ∧ (p2 ∧ False))) ∨ False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184095158105668900829441140136 : (((((p3 → True) ∨ p4) → ((p4 → (p5 ∨ p5)) ∧ p2)) ∨ p5) ∨ (((p3 ∨ (p2 → p4)) → (((False ∧ False) ∧ p2) → False)) ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215285415713972307608546170371 : ((p1 ∧ ((p3 ∧ p4) ∧ False)) ∨ (p1 ∨ ((p1 ∨ ((p5 → (p3 ∨ False)) → True)) ∨ ((((p1 → p1) → p2) ∨ (p2 ∧ p4)) ∧ (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_658510108095336741864740674316 : ((((p2 ∨ (((((p5 ∧ p5) ∧ (True ∧ (p2 ∧ False))) ∧ (p2 → False)) ∧ ((p5 ∧ (p3 → (True ∨ p3))) → p4)) ∨ p1)) ∨ (True ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_610423331459158052496985715538 : (((((((((True ∧ (p1 ∧ p2)) → p3) ∨ (True → p4)) ∧ ((((True → (False ∨ (p2 ∧ False))) ∨ p1) ∧ p2) ∧ p2)) → p3) → p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_227763396007384346386812468525 : ((p1 ∧ (p5 ∨ p3)) ∨ ((p5 ∨ (p4 → (p5 ∨ p4))) ∧ (p5 → (((((True ∨ ((p4 ∧ p4) ∨ p3)) ∨ p3) ∨ p4) ∨ (p1 → True)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309908605701994452532109121290 : (p2 ∨ ((((p1 ∨ (((p2 → p5) → (True → ((p2 ∨ p5) ∨ True))) → (True → p5))) → p1) ∧ p4) ∨ (((True ∨ p4) ∨ (p1 ∨ p2)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137263762284745439487731029022 : ((p1 ∧ (p2 ∧ ((p1 ∧ (p4 ∨ p3)) ∧ (p2 ∨ ((p3 ∧ p4) ∨ (((p4 → p5) ∨ ((p4 ∨ p5) → True)) ∧ p1)))))) ∨ (p2 → (p2 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314640690169767762482354178084 : (p3 ∨ (((p5 ∨ ((False → ((p2 ∧ ((p4 → (p1 ∧ False)) → False)) ∧ p5)) ∨ False)) ∧ p3) ∨ (((p1 ∧ (p5 ∨ p3)) ∧ p2) → (p1 ∨ p4)))) := by
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
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54540688282675819775399638657 : ((((p1 → p4) → ((p5 ∧ (p5 ∧ p4)) ∨ p4)) ∨ ((((p5 ∧ (p4 → (p2 ∧ (p2 ∨ p4)))) ∧ p4) → (p4 ∧ (p1 → p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165927313304809255286940523513 : (((p3 ∧ p2) ∧ ((p2 → (False ∧ ((p1 ∧ ((True ∨ p4) ∧ (p1 ∨ True))) ∨ False))) ∧ True)) ∨ ((True ∧ p5) ∨ ((True ∨ p1) ∨ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205032752931810225942726984809 : (((p4 ∨ (p5 → (p4 ∧ p3))) → p5) ∨ ((((p4 ∧ False) ∧ (p4 ∨ p4)) ∧ (True → (p2 ∨ (p5 ∨ p1)))) → (p2 ∨ ((p2 ∧ p3) ∧ p2)))) := by
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
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67409744724249612150942789869 : ((p1 → ((p5 ∨ (p1 ∧ ((((p5 → p5) ∨ False) ∧ (p5 ∧ p2)) ∨ (p2 → (p4 ∨ (p4 ∨ (p1 ∨ (p4 → p3)))))))) ∧ (p1 → True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39933743306472252432810106331 : (((p3 → (p2 ∧ ((p2 ∨ (((p3 ∧ (p3 ∨ p2)) → (p5 → (p4 ∨ True))) ∨ p5)) ∧ (((p1 ∨ (p3 → p1)) ∧ p4) ∧ False)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131875780667910555680962543643 : (((p1 ∧ p3) ∨ (((p5 ∧ ((((p1 → True) ∨ p2) ∧ ((p2 → p1) ∧ False)) ∨ p4)) ∨ (p5 → (True ∨ p3))) ∨ p2)) ∧ (True → (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341964368766556167215877380143 : (p2 → (((p1 ∨ ((((True ∧ True) ∨ ((((False → (p2 → True)) ∧ (p4 ∧ p3)) → p1) ∨ False)) ∧ p4) → False)) ∧ False) ∨ (p3 ∨ (p3 → True)))) := by
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
theorem thm_5_vars_193926449302439284879616089768 : ((p1 ∨ (True ∨ (p5 → (p1 ∧ ((p5 ∨ True) ∨ p1))))) → ((True ∧ True) ∧ ((p2 → ((p1 ∧ p2) ∨ (p1 ∧ (True ∨ (False ∧ p1))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_138380047206010189579326775300 : ((p4 → ((True ∨ p3) ∧ (((p4 ∨ p4) → (((True ∨ False) → (p2 ∧ p2)) → False)) ∨ ((p5 ∧ (p3 ∨ p1)) ∧ p2)))) ∨ (False → (True ∧ p5))) := by
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
theorem thm_5_vars_218094576549633439205915123345 : (((False → True) ∧ (p1 → False)) → (p5 ∨ ((((p3 → (p3 → (False ∨ p3))) ∧ p3) ∨ ((p2 ∧ False) ∨ p2)) ∨ (p1 → (False ∨ (p2 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167652268039804967146466545938 : ((((p3 ∨ True) ∧ (((p3 ∨ p2) → False) ∧ (((p2 ∨ False) → p4) ∨ p2))) → (p5 → p4)) → ((p4 ∧ p1) → (((p1 ∧ p1) ∨ p1) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739227743568707592358599481818 : ((((p4 ∧ p1) ∨ (((True ∧ p5) ∨ (((p3 ∧ True) → True) ∨ p2)) ∧ (p5 ∧ (p5 ∨ (p5 → (((p3 ∧ p4) ∨ p4) ∧ (p3 → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198285123272938692457353467336 : ((False ∧ (True → ((p2 → (p2 → p3)) ∧ p1))) ∨ ((((p2 → (p1 → p5)) ∧ p1) ∨ (p3 → (p4 ∨ p4))) → ((p4 → False) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_352229764103098675738191341596 : (p4 → (((p5 → (True ∨ p5)) → False) ∨ ((((p4 ∧ False) ∧ ((True → p4) ∧ True)) ∧ (p2 ∨ p5)) ∨ (((p4 ∨ False) ∧ (p5 ∨ p2)) ∨ p4)))) := by
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
theorem thm_5_vars_114970321592002030851227873748 : (((p5 → (p3 ∨ (((False → True) → (True → p2)) → (p5 → (p1 → p1))))) → ((False ∧ p3) ∨ (p4 ∧ ((p5 ∨ p3) ∧ p3)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585626811624716994169241341452 : ((((((p5 ∨ ((((p1 → (p2 ∧ p2)) ∧ (p5 ∧ p4)) ∨ p1) → ((p3 ∨ ((True ∨ (True ∨ p4)) ∧ False)) → p2))) ∨ False) ∧ p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310799681828823963633731334534 : (p2 ∨ ((p1 ∧ (p1 ∧ True)) ∨ ((p5 ∧ ((p1 ∧ True) ∨ p3)) → (p3 ∨ (((((p4 ∨ False) ∨ p5) ∨ p5) ∨ (p3 ∧ (p2 → True))) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147650833606898080873492641031 : (((((p3 ∧ ((p3 ∧ ((((p5 → False) → p2) → p2) ∨ (p4 → p3))) → False)) → p3) ∧ (p4 ∧ p4)) → False) ∨ ((p2 → (True ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324070152501216676739293173189 : (p5 ∨ ((((True → p2) → ((p1 ∧ p4) ∨ (p4 ∨ (p4 ∧ p5)))) ∧ True) ∨ ((p4 ∧ p3) ∨ ((p1 ∨ p5) → ((True ∧ (p5 → p5)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345669014245041750782185803451 : (p3 → ((False ∨ (p3 → (((p2 → (((True → False) ∨ p2) ∧ (((p4 ∨ True) ∨ p1) ∨ p4))) ∨ (p3 → (p4 → True))) ∧ (p4 ∨ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56549792943456575540084478717 : (((p3 ∨ ((p3 ∨ p4) ∧ True)) → ((((((False ∧ p1) ∧ (p2 ∧ ((p1 ∧ (p4 → p5)) ∨ False))) ∧ False) ∨ p5) → p3) ∧ (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150894337086307968950985179247 : ((((p3 ∨ (p4 ∧ p2)) ∧ (((True ∧ (True → p2)) → (True ∨ ((p3 ∨ (False → False)) ∨ p5))) ∨ p3)) ∨ False) → (((p5 ∨ p5) ∨ True) ∨ p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45883041638950986633553688214 : (((p3 → ((p4 ∨ p5) → (((True ∧ (p3 ∨ p1)) → (False ∨ False)) → (p2 ∨ ((((False → False) → p3) ∨ False) → (p3 → True)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337983776487582398068362064370 : (p1 → (((p3 ∨ (p5 ∧ False)) → ((p1 ∧ (False ∧ (True ∧ p5))) → p2)) → ((((p2 → True) → p4) ∨ p4) → ((p4 ∨ (p1 ∧ p1)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609017905376511048028237514741 : (((((((((p4 ∧ False) ∨ (True ∨ (p5 → p5))) → p4) ∨ p2) → (p4 ∨ (p3 → ((p5 ∧ (p5 ∧ (p4 → p3))) ∨ True)))) ∨ p1) ∨ p1) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717064568591162672499123155147 : ((((True ∨ ((p5 ∧ p5) ∨ False)) ∧ ((p3 ∨ (True ∨ False)) ∧ ((((((True ∨ p2) → (p5 ∧ p3)) → p2) ∨ p1) → (p2 → p5)) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349336723801905843655596093727 : (p3 → (p3 → (((False ∧ p3) ∨ (((p3 ∧ (p4 ∨ ((p2 ∨ (p2 ∧ (p1 → (p2 ∨ p2)))) ∧ True))) → p4) ∨ ((p5 ∧ True) ∧ p1))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113184067645088616811900166610 : (((((((((True → False) ∧ (p5 ∧ (p1 ∧ (p4 ∨ False)))) ∧ p2) ∨ True) ∨ p1) ∨ (True → (p1 → p1))) ∧ p4) ∧ (p2 → p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156917450318179758097983644111 : (((((p5 → ((p2 ∧ True) ∨ False)) ∨ ((p2 → (p2 → (True ∨ (p3 → p5)))) ∧ p2)) → p5) ∨ False) ∨ ((False → p2) ∨ ((p3 ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68061652427514424543299435150 : ((p2 → (False ∨ ((p5 ∧ ((p3 → p1) ∧ ((p1 → p3) → (p1 → p4)))) ∨ (p1 → (((((p2 → True) → p1) → p1) → p1) ∨ p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45778845833994352466689669444 : (((p1 → (((p5 ∧ p4) ∨ ((False → (p4 → (p4 ∧ (((p2 ∨ (False ∧ False)) → True) → (p4 ∨ False))))) ∨ (True ∨ p4))) ∧ p5)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257564708335422512880252940973 : ((p3 ∨ p1) → (((((True ∨ p1) → (p4 ∧ p4)) ∧ (((p1 → ((p1 ∧ (p1 → p3)) ∨ p5)) ∨ True) → p5)) → p5) ∨ (p3 → (False ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 → ((p1 ∧ (p1 → p3)) ∨ p5)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p1 → ((p1 ∧ (p1 → p3)) ∨ p5)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22167737454987052319492501176 : ((((p2 ∨ p3) ∨ (False ∨ (p3 ∨ (p5 ∧ p4)))) ∨ ((p4 ∨ ((p5 ∨ p4) ∧ (True → (False ∨ (((p4 ∧ True) ∧ p3) ∧ False))))) → p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259080068682564554012541133416 : ((True → p5) → ((p3 ∨ (((p1 → p5) → (((False ∨ p4) ∨ (p3 ∨ True)) ∧ p5)) ∨ (p3 ∨ (p4 → (False → (False → p5)))))) ∨ (p3 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122060091234261081998188824853 : (((p2 → ((((((p5 → p3) ∧ ((p5 ∨ p3) ∧ (p2 ∨ ((p1 ∨ p4) → False)))) ∨ p5) → (True ∧ True)) → p1) ∨ True)) → False) → (p3 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((((((p5 → p3) ∧ ((p5 ∨ p3) ∧ (p2 ∨ ((p1 ∨ p4) → False)))) ∨ p5) → (True ∧ True)) → p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → ((((((p5 → p3) ∧ ((p5 ∨ p3) ∧ (p2 ∨ ((p1 ∨ p4) → False)))) ∨ p5) → (True ∧ True)) → p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193363449630913129229468908917 : (((True ∨ (p1 ∧ True)) → (p5 ∧ (False ∧ (True ∧ p4)))) → (((p5 ∧ ((p5 → (((p1 → False) ∧ (p4 ∨ p2)) ∨ p3)) ∨ p4)) → p3) ∧ p3)) := by
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
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (p1 ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ (p1 ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (True ∨ (p1 ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248452414381766384296850427166 : ((p2 ∨ p5) ∨ ((p5 ∨ ((p3 ∨ ((False → p5) ∨ (True ∧ (((p1 ∧ False) ∨ p3) ∨ (p4 ∨ False))))) ∧ ((p3 ∧ True) ∨ False))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305870535921972147180467637168 : (p1 ∨ ((((p1 ∧ p5) → (p5 ∨ True)) → p4) ∨ ((p2 → ((True ∧ ((True ∧ p1) ∧ (True ∨ p5))) ∨ p3)) ∨ ((p3 → True) → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600341788377331201800604779011 : ((((True ∧ ((((p1 → (True ∧ False)) → ((p5 → (p1 → p2)) ∧ p5)) → ((p2 ∧ (False ∧ (True → False))) ∨ (False ∨ p5))) ∧ p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914286023287990644221741880545 : ((((((p1 → (p5 ∧ (p2 ∧ p4))) → (False ∨ ((True ∧ p1) → p3))) ∨ (False → p4)) ∧ (p3 ∧ (((p5 ∨ False) ∨ (p3 → p2)) ∨ p2))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216082243496616318614451576743 : ((True → ((p3 ∨ True) ∧ False)) ∨ ((((((p4 ∨ False) → p3) ∨ ((p4 ∨ True) → (p4 ∧ (True ∨ p1)))) ∧ True) ∧ (False ∧ p4)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328117869994819838418581408215 : (True → (((p5 → (((p2 ∨ False) ∧ p3) → ((((False → p2) → p1) ∧ False) ∧ p4))) ∧ (p4 ∧ ((p2 → p1) → p2))) ∨ ((True ∨ p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57360736318329028466700432306 : (((p3 ∧ (p5 → p3)) ∨ ((((p4 → p2) ∨ (p3 → p4)) → (p1 ∧ (False → ((((True → p5) ∧ p4) ∧ p5) ∨ (p5 ∧ p5))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40545727688825404130958514261 : ((((p5 ∨ ((True ∨ p5) ∧ ((((p3 ∨ (p2 ∨ p1)) ∨ ((p4 ∨ ((p2 ∧ p4) ∨ p4)) ∨ p1)) ∨ (True ∨ p1)) ∧ p3))) ∨ True) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249751731520822748070009824339 : ((p5 ∨ p5) ∨ ((p5 → p5) → (((((((p3 ∨ (p4 ∨ (p1 ∧ (True → True)))) ∧ p2) ∨ p5) ∧ False) ∧ (False → (False ∨ p3))) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646554785497350356391111723971 : ((((p1 → (((p1 → p5) ∨ (True ∧ p2)) ∧ (False → ((p2 ∨ p3) ∧ (True ∨ (((p1 → (p1 ∧ True)) → (p3 ∧ p2)) ∧ True)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608318706162576784404805693876 : (((((((p3 → ((p3 ∧ p1) → ((False → True) ∨ p2))) → ((((True ∧ p4) → ((p1 ∨ False) ∧ p4)) → p5) ∨ p2)) ∨ True) ∨ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624948240301742588275300281109 : ((((p5 ∨ (p1 ∧ (((p5 ∨ (p4 → (p4 ∨ ((False ∨ (True → (p5 → (True ∧ p4)))) → p1)))) → (p4 ∧ True)) → (p1 ∧ p4)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261152403265955864451891565363 : ((p4 → p4) → (((True ∨ ((p5 ∧ (p1 → ((p5 ∧ p3) ∧ True))) → ((p1 ∧ p2) ∧ p1))) → p2) → ((False → True) → (True ∧ (p2 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((p5 ∧ (p1 → ((p5 ∧ p3) ∧ True))) → ((p1 ∧ p2) ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63010470639482624478654555534 : ((p4 ∧ (p2 → ((p4 ∨ ((p1 → ((p5 ∨ p5) ∨ (p1 ∧ ((p1 ∨ p4) ∨ p3)))) ∧ (True → p1))) ∧ ((p1 ∧ (True → True)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309359666318961813890006952708 : (p2 ∨ (((p2 ∨ (((p4 ∧ p1) ∧ False) ∨ True)) ∧ (((False ∨ False) → ((p4 ∨ (p2 ∨ ((p1 → p4) → p3))) ∨ p1)) ∨ p4)) ∨ (p4 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119081301243632595306438411209 : ((p1 → (((p5 → p3) ∨ (p4 ∨ (p5 ∨ ((True ∨ p5) → (((False ∨ p3) ∨ True) ∨ p5))))) ∧ ((p5 ∨ (p1 → True)) ∨ p2))) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351410527107157614330100410873 : (p4 → ((((False → (p5 → p2)) → p1) ∨ ((((False ∧ (p4 → False)) ∨ False) → (p2 → True)) → (p5 ∧ p5))) ∨ ((p3 → True) ∧ (p4 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179090306185804777984857537327 : ((False ∧ ((((p1 → (p2 ∨ ((p3 ∧ False) → p3))) ∧ p2) ∧ False) ∨ p1)) ∨ ((((True ∨ p3) ∨ p3) → (((p4 ∧ p5) ∧ p2) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622274219070179303898753784672 : ((((p3 ∧ ((((False ∧ p5) → ((p2 ∨ (True ∨ (p4 ∧ False))) → p2)) → ((True ∧ ((p3 → p4) → p1)) ∧ (p1 ∧ p5))) ∧ False)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



