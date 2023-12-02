variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171479661847009870992887362686 : (((p5 ∨ ((((p2 → p2) ∧ (p4 ∧ p4)) ∧ p4) → (p2 ∧ (p5 ∨ p5)))) ∧ True) ∨ (True → (p2 ∨ (((True ∧ (False ∨ False)) ∧ p1) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313405382559581788464821834108 : (p3 ∨ (((p2 ∧ ((((((((((p1 ∨ p3) ∨ p5) ∧ (p2 ∧ p5)) ∨ True) ∨ True) ∧ (False ∧ p2)) ∨ False) ∧ p4) ∨ p2) → p1)) ∧ p4) → p1)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((((((p1 ∨ p3) ∨ p5) ∧ (p2 ∧ p5)) ∨ True) ∨ True) ∧ (False ∧ p2)) ∨ False) ∧ p4) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251583804351971273477339018415 : ((p3 → False) ∨ (p4 ∨ ((p3 → True) ∧ (((p1 ∧ (p5 → p2)) ∨ (((p2 ∨ (True ∧ (p3 → p3))) ∨ ((p4 ∨ True) ∨ p5)) → p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695223147764853891371934288781 : (((((p5 → (p1 → ((((False → p3) ∨ p4) → p3) → (p3 ∨ p3)))) ∨ p4) → ((((p2 ∨ False) → (p1 ∨ True)) → (False → p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263154102577645279876732888339 : (True ∧ ((p1 ∧ (((p2 ∨ (False ∧ p3)) ∧ True) ∨ (((True ∧ (p2 ∧ (p3 ∨ (p4 ∧ True)))) ∨ p4) → (False → (True → p3))))) ∨ (p4 ∨ True))) := by
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
theorem thm_5_vars_614729053448125264784768845681 : ((((((False ∧ (((p1 ∨ p2) ∨ (p2 ∨ ((p4 → p5) ∧ p4))) → (p5 ∨ p3))) ∨ (p4 ∨ False)) ∨ ((True ∧ p4) → (p2 ∨ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_191526851975699248537140758388 : ((False ∧ (p4 ∨ ((p3 → True) ∧ (p4 ∨ (p3 ∨ p4))))) ∨ ((False ∨ (p2 ∧ (p5 → ((p4 ∨ p5) → (p1 ∨ p2))))) ∨ ((p3 ∧ p2) → p3))) := by
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
theorem thm_5_vars_225603767987188618902100404801 : (((p1 → True) ∧ p3) ∨ ((((p5 ∧ (p1 ∨ p4)) → ((((True → p4) ∨ p4) ∧ p4) → p2)) ∨ (True ∧ (p3 ∨ (p4 ∧ (p5 ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306143871402530257072852875244 : (p1 ∨ (((p5 ∧ p5) ∧ True) ∨ ((p1 ∧ True) ∨ (((((((p2 ∨ (p1 → p3)) ∨ (True ∨ p4)) ∧ p2) ∨ p2) → False) → (False ∨ False)) ∨ True)))) := by
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
theorem thm_5_vars_319154630080359535837528898916 : (p4 ∨ (((((p4 → p1) ∧ (((False → (p3 → (p2 → (p4 ∨ p2)))) → p5) ∧ True)) → p3) ∧ p5) ∨ ((p4 → p5) → (True ∨ (False ∨ p2))))) := by
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
theorem thm_5_vars_180739758235959266063241152276 : (((((p5 ∨ False) ∨ False) → p2) ∨ (((p3 → p1) → (True → True)) ∨ p3)) → (p1 ∨ ((p2 ∨ (((p5 → p2) ∧ p1) → True)) ∨ (p2 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687981451563036965448215925285 : ((((((((p4 ∧ p1) → p5) → p4) ∧ p5) ∧ ((p2 ∨ p3) ∨ ((p1 ∨ p4) ∧ p5))) ∧ (p3 → (False ∧ ((p5 → (p2 ∨ True)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685917143408900165157448582193 : (((((((p1 ∨ ((p4 ∨ (p1 ∧ False)) → (p5 → (p1 ∧ p3)))) ∨ True) ∧ p2) ∧ (False → p5)) → (((True → True) ∨ (p1 ∧ p2)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355874935589095866376238408762 : (p5 → (((p3 ∨ p4) → ((((True ∨ p3) → (p5 → p2)) ∨ (((False ∨ p5) → (p4 ∨ p2)) → (p1 → p3))) ∨ p4)) ∨ (p1 ∧ (p5 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_58845159781275337007981547797 : (((True ∧ p2) ∨ ((p2 ∨ ((True ∧ (p3 ∧ ((p5 ∨ True) ∨ ((p2 ∨ (True ∧ False)) ∨ (p4 ∧ ((True ∧ p2) → True)))))) → p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194032619262207605826412265631 : ((p5 ∨ (((True → p2) ∨ ((True ∨ p5) ∧ True)) ∧ True)) → (((p2 → p3) ∧ p2) → ((p3 → (((p5 ∨ False) ∧ p2) ∧ (p1 ∧ True))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h11
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h23 : p3 := by
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h25 := h4 h24
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h23
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219441102596096503949769016214 : ((p4 ∨ ((p4 ∧ p5) → p5)) → ((p2 ∨ p2) → ((((False ∨ ((p2 ∧ ((p3 → p1) ∧ p5)) → ((p1 → False) ∧ p3))) ∨ p2) ∧ p3) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205064095649395832745969225915 : (((p3 → ((False ∧ p4) ∧ p1)) → p3) ∨ (p3 → ((p2 ∨ (((p2 → False) ∨ p1) ∨ (((p1 ∧ p5) → False) → False))) → (True → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655579540922598388003000643060 : (((((((p2 → p1) ∨ p1) ∨ ((p4 → ((p2 ∨ ((True ∧ p5) ∧ (p3 ∧ p4))) ∧ True)) → (p5 ∧ p5))) → (True ∧ p2)) ∨ (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115126046121667281683012036370 : ((((p2 → (((False ∨ p2) ∨ p2) ∧ p1)) → (p4 ∨ (p5 → True))) → (((((True ∨ (p1 ∨ p1)) → p5) ∧ p4) ∧ False) ∨ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119516524928156860777263064746 : ((p5 → ((((p1 ∧ (p2 ∧ ((p1 ∧ True) ∧ ((p1 → p1) → False)))) ∧ ((p2 → False) ∧ ((p5 → p5) ∧ p1))) ∧ p3) ∨ p2)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136109837469036207197584331217 : ((((p1 → (p1 ∨ p4)) → (p1 ∨ (p3 ∧ p2))) ∨ (((True ∨ (p4 ∨ ((p5 ∨ p4) ∧ p4))) ∨ p1) ∧ (False ∨ p3))) ∨ ((p2 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678861760998882018651033607933 : ((((p1 ∧ ((p5 ∧ p5) ∧ (p5 → ((p1 ∧ ((p5 ∨ p2) ∧ (False ∧ (p5 ∨ (p4 ∨ p3))))) ∨ p2)))) ∨ ((p2 ∧ (p1 → True)) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_118809358397715268635644954978 : ((True → (((p2 ∧ (((((p4 ∨ ((p3 ∨ (((p4 ∨ p3) → True) ∧ p2)) ∧ True)) → p4) ∨ p4) → p5) → p3)) ∨ True) ∨ p2)) ∨ (p5 ∧ False)) := by
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
theorem thm_5_vars_52688937838742867898946602699 : (((True → ((p4 ∧ ((p2 ∧ p1) → ((p3 → (p2 ∨ p5)) ∧ p4))) ∨ p2)) ∨ (p2 ∨ ((((p1 → (p1 ∨ p1)) → p2) → True) ∨ p3))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199290284469853476584089612642 : ((((p2 → ((p4 ∧ p2) → p1)) ∧ p5) ∨ False) → (p2 ∨ ((p1 ∧ (p1 ∨ (((False → p1) → True) ∧ (p5 ∨ p3)))) ∨ ((False → p1) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68435832277033975707073286656 : ((p3 → ((False → True) → (((p1 ∧ ((p2 ∨ p3) ∧ ((p2 → (((p5 ∧ False) → False) → p4)) ∧ p1))) → p3) → ((True → p1) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704338552264146649981372685276 : (((((((p4 ∨ True) ∧ p1) ∧ p5) → (p2 ∨ (p2 ∨ p1))) → (True → (((p2 ∨ (p5 → ((p4 ∨ (False ∨ p3)) ∨ p3))) → p1) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41354980852273644171230878928 : ((((((((p3 ∧ (p4 ∧ (p4 → False))) → (p3 → (p5 ∨ p2))) ∧ p5) → p4) ∧ p1) → ((p3 ∧ True) ∧ (p1 ∨ (False → p3)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65543094508268735351380712045 : ((p3 ∨ (True → (((((((True → True) → p3) ∧ p4) ∨ p5) ∧ ((True ∧ p5) ∨ (((True ∨ False) ∧ True) ∧ (p2 → p3)))) → p4) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346959398755685379851323324222 : (p3 → ((p5 ∧ (p2 ∧ (p3 → ((False ∧ ((p5 ∧ False) ∧ ((p2 → (False ∨ p1)) ∨ p3))) → p5)))) → (((p3 → (p4 → p1)) ∨ p5) ∧ p5))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171662846355937655207753776666 : (((p3 ∧ ((p4 ∧ (p2 ∨ (p4 ∧ False))) ∨ ((p3 → p5) → (p3 ∨ p1)))) ∨ p4) ∨ (((p1 ∨ (p5 → (True → p5))) → (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248431204511199629033129581771 : ((p2 ∨ p4) ∨ (p4 → ((((((p3 ∧ p1) ∨ (True → p1)) → p1) → (((p5 ∨ p4) ∨ (p4 ∧ p2)) ∧ True)) → (p3 ∨ p1)) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61475131484519316400123846629 : ((p1 ∧ ((((((((False → ((p2 ∧ p2) ∧ p4)) ∧ False) → True) ∧ True) ∨ p5) → p4) → ((True → p3) ∧ (p4 → False))) → (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636327790499219132876407886824 : ((((((((p5 ∧ (p2 ∨ ((p2 ∨ p1) ∨ False))) ∨ (True ∨ True)) ∨ p5) ∧ (p5 ∧ p1)) → ((True ∨ (True ∨ (p3 ∨ p1))) → p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178811192754898737013586506833 : (((p1 ∧ (p1 ∨ p2)) ∨ (((p3 ∧ p1) ∨ True) → ((p3 ∨ p5) ∨ p2))) ∨ (p2 ∨ ((False → (p5 ∧ (p4 → p5))) ∨ ((p2 → p3) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191367723643756461215085596057 : (((True → p3) ∨ (p1 ∧ ((p4 ∧ p1) ∧ (True ∨ False)))) ∨ (((p2 ∧ True) ∨ p5) ∨ (True ∧ (((p3 ∧ p2) ∧ p1) ∨ ((True ∨ p5) ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725419368676825223559335655387 : ((((p5 → (p2 ∧ p1)) ∧ ((p4 ∨ ((((p2 ∧ (True ∨ p3)) ∧ p3) ∧ (p3 ∨ p2)) ∨ ((((False ∨ False) ∨ p5) ∨ False) ∧ p4))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201285519220509501840063665761 : ((p4 → ((((p4 ∨ p5) → False) → True) ∨ False)) → (((((True → False) ∧ p2) ∨ (p2 ∨ True)) ∧ (p3 → (((True → p1) ∨ p3) → p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164665541064343156870278661744 : (((p5 → ((p5 → ((p2 ∧ (((True ∨ p4) ∧ p2) → (p5 → p4))) → p4)) → p4)) ∧ p1) ∨ (((p3 → False) ∨ ((p4 → p2) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326359946299660417823539066163 : (p5 ∨ (p5 → ((((True ∨ (p4 ∨ ((p2 ∧ p4) → (p4 ∨ False)))) ∧ p4) → ((p3 ∨ False) ∨ p4)) ∧ (((p2 → True) → True) ∨ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161624280593285727644671747606 : ((False ∨ ((p4 → False) ∧ ((((p1 ∧ (p4 → p3)) ∨ False) ∨ (True ∨ ((p3 ∧ p4) ∨ p3))) ∨ p2))) → ((False ∨ (True → p2)) → (p2 ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h14 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h15 := h4 h14
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h19 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h20 := h4 h19
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h22.left
              let h24 := h22.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h24
            case inr h25 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h26 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h27 := h4 h26
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h27
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322245893062934238364324756094 : (p5 ∨ ((((p2 ∧ (p5 → ((True ∨ p1) → (((p3 → (p1 → p3)) ∨ p3) ∧ (((p1 → p1) ∨ (p3 ∨ p5)) ∨ p2))))) → p3) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51489429306167235359140377976 : ((((p5 → ((p5 ∧ p4) ∨ p2)) ∧ (p1 ∨ ((False → (((p2 → p1) ∧ True) ∨ p2)) → p3))) → ((p4 → True) ∧ (False ∨ (p5 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341008612361175339339585238951 : (p2 → ((p1 ∧ ((((p4 ∨ (p1 ∨ p5)) ∨ False) ∧ ((p2 ∨ (p2 ∧ p1)) ∨ ((p3 ∨ p5) ∨ (False ∨ (p1 → p1))))) ∨ (p3 ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239151993029540383505277765788 : ((p2 ∨ True) ∧ ((p3 → (p1 ∧ ((p2 ∧ (((p2 ∨ p5) ∧ ((False ∧ p1) → (((True ∨ True) ∨ (True ∧ p1)) ∧ p4))) ∨ p5)) ∨ p5))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150235007758547554881277200589 : ((p3 → (((False ∧ (p4 ∨ True)) ∧ (p5 ∧ ((((p4 → ((True ∧ True) ∧ p4)) ∧ False) ∨ p2) ∧ p1))) ∧ p1)) ∨ ((p4 → (False ∨ p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48200581806032881218606741989 : ((((True ∧ p4) → (p1 ∧ (((((p1 ∧ p3) ∨ ((p2 ∨ ((p5 ∨ p2) → (p1 ∧ p4))) ∨ p5)) ∨ p2) ∧ p4) ∧ p5))) → (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147429697397871900895395644787 : (((((p4 ∨ p4) ∧ p4) → (p5 ∨ (((p5 ∨ p4) ∧ ((False ∨ p2) ∧ (False ∨ (p4 ∧ p1)))) ∨ True))) ∨ p5) ∨ ((False ∧ True) → (p4 → p3))) := by
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
theorem thm_5_vars_305546393475993368843366072137 : (p1 ∨ ((p5 → ((p2 ∨ (False → (p5 → ((p2 → p1) ∧ (True ∧ p1))))) → p4)) → (p1 → ((p4 ∨ ((False ∧ p5) ∧ (p3 ∧ p1))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611779223936888049895927422320 : (((((p1 → (((True ∨ p3) ∧ (((p3 ∨ (p5 ∧ p2)) → (((p1 → p4) ∨ p3) → (p1 → (p1 → p3)))) → p4)) → p1)) → p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_165365728977222171066239570459 : ((((p1 ∧ ((False ∨ (False ∧ p3)) ∨ ((p3 ∨ False) ∨ p4))) ∧ p2) ∨ (False → (p2 ∨ p1))) ∨ (p3 ∧ (p5 → (p4 → (p5 → (p4 ∧ p4)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46833797198389202094711298342 : ((((((p3 ∨ p2) → (((p1 ∧ (p1 ∧ p2)) ∧ True) ∧ (True ∨ (p3 → p1)))) → (True → (p5 → (True → False)))) ∧ p1) ∨ (True → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204766715798171871578873820706 : (((((p2 ∨ p5) ∨ p4) ∧ p3) → p1) ∨ ((((p2 → (((p1 ∧ p4) ∧ ((False ∨ p2) → p2)) → p5)) ∨ p3) ∨ p2) ∨ ((p3 ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50263673061862866150790649199 : (((((False ∧ (((p4 ∧ (False ∧ (p3 ∧ (True → p5)))) ∨ p4) ∨ (False ∧ p2))) ∨ p1) ∧ (True ∧ p3)) ∨ ((p2 → (p1 → p2)) ∨ p1)) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308370344014625810327861930247 : (p2 ∨ ((((((((p2 ∨ p4) → (((p3 ∧ ((False ∧ False) → p5)) → (p2 ∧ True)) → p3)) ∧ p1) ∧ (p4 → p5)) ∧ p5) ∨ True) ∨ False) ∨ p5)) := by
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
theorem thm_5_vars_310845912743838930841241991288 : (p2 ∨ (((p2 ∨ p1) ∨ p3) → (True → (True ∧ (((p1 ∧ p1) → ((True ∨ (p4 ∧ (True ∧ True))) → False)) ∨ (True ∨ (p3 ∧ (p2 ∧ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63934544525471442187873392732 : ((False ∨ ((((((True → (True → (True → (p1 ∧ p5)))) ∧ p2) ∨ ((p2 ∨ p3) → p3)) ∨ (True ∧ False)) ∧ (p5 ∨ (p3 ∧ p5))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184320355397069831188890329085 : ((((p3 ∨ p2) ∨ (p1 → (True → ((p2 ∧ p1) ∨ p4)))) → p3) ∨ (False ∨ (((p2 ∧ p2) ∨ (((False ∨ False) ∨ p1) ∧ p3)) → (False → p4)))) := by
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
theorem thm_5_vars_322487819370332039095934880653 : (p5 ∨ (((p4 ∨ p1) ∨ (((p5 → (p4 → p1)) ∨ (False → p3)) → (p2 ∧ (p2 → (p5 → (p3 ∧ ((p4 ∨ p2) → (p1 ∧ p4)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707290223703869701551585809992 : (((((p2 → (p5 ∨ (p3 ∨ p4))) ∧ (p2 ∨ p3)) ∨ (p2 ∨ (p1 → (True ∨ (p2 → ((False ∧ (p5 ∨ p2)) → (p1 ∧ (False ∧ True)))))))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59295256174676847226086741143 : (((p3 ∨ p5) ∨ ((((p2 → (p1 ∧ p5)) ∨ ((True ∨ (p1 ∨ False)) → (True ∧ ((False ∧ p5) ∨ (True ∨ p2))))) ∨ p4) ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60097144400132118450064154907 : (((p3 ∨ False) → (True → ((True ∨ p5) → (((False ∨ p4) ∨ False) ∨ (((((p1 ∧ p1) ∨ p2) ∧ p2) ∨ p4) → ((p5 → p2) → p3)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h29 =>
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55100292109315318619686815274 : (((p4 → ((False ∧ False) ∨ (True ∧ p2))) ∧ (True ∧ (False ∧ ((((p5 → p3) ∨ p1) → (True ∧ p5)) ∧ (True ∧ ((p5 ∨ p1) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225180575808395628869319319098 : (((p4 ∧ p1) ∧ p1) ∨ ((((p2 → (p5 ∧ p4)) → p5) ∧ (((p4 → (((p4 ∧ False) → p1) ∨ (p4 ∧ True))) → p3) → p3)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324076912805951647640749985443 : (p5 ∨ (((False → (p5 → ((((p5 ∧ False) ∧ p3) → p2) ∨ False))) → p3) ∨ ((p2 ∧ (p1 ∨ (p1 ∧ ((p3 ∧ p3) ∧ (False → p2))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116800557278905399648451144524 : (((p2 ∨ p5) ∨ ((p3 ∧ ((p3 ∨ ((False → (p3 ∧ (p3 ∨ ((True ∨ p4) ∧ True)))) → (p5 ∨ p4))) → p2)) ∧ (p5 ∨ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309602562612823461867619419567 : (p2 ∨ (((p2 ∧ ((True → (p2 → True)) ∧ ((p5 ∧ (False ∧ (p4 ∨ (p1 → True)))) ∧ ((False → False) ∧ True)))) ∧ p2) ∨ (True ∨ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90675361991740329366306665896 : (((True ∨ p5) ∧ (p5 ∧ (True → (((((p5 ∧ True) → p3) ∧ (False ∨ p4)) ∨ (p2 → ((p3 → ((p3 ∨ True) ∧ True)) ∨ p2))) ∧ p1)))) → p1) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313189522980691389390231995004 : (p3 ∨ (((((p4 ∧ (p3 ∨ p2)) ∨ False) → p5) → ((((p5 ∧ p3) → True) → p2) ∨ (((p1 → p5) → ((False ∧ p2) ∨ p1)) ∨ True))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117364825514271423430114125766 : ((False ∧ (p3 ∨ ((p4 → p3) ∨ (((((False ∧ (p1 ∨ True)) ∧ p1) → (p5 ∨ p4)) ∧ (True ∧ p5)) ∧ (p1 ∧ (p2 → False)))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46903731616529449554585849821 : ((((((p1 ∨ (((p3 ∨ False) → (p3 → (p1 ∨ True))) ∨ (p4 → p4))) ∨ (p2 ∧ (True → p2))) → (True → p1)) ∨ True) ∨ (True ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265560677038671134874074465800 : (True ∧ (False ∨ (True → (((p4 ∧ (((p3 ∨ (False → (p3 ∧ p2))) ∧ p2) → p5)) ∨ p2) ∨ (p2 → ((p3 ∧ True) → ((True ∨ p2) ∨ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60257698104620527215908678832 : (((False → p1) → (((p4 ∨ (p3 ∨ p4)) ∧ (False ∧ ((True ∧ p3) ∨ (p2 ∨ False)))) ∧ (True ∧ (((p1 ∨ p1) → (p3 → p1)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78750711467538983393333767543 : ((((p2 → ((p1 → p2) ∧ (((False ∧ p5) → p1) ∧ False))) ∨ (False ∨ ((p2 ∨ p3) → ((p3 ∨ p5) ∧ (False ∧ p3))))) ∧ (p2 ∧ p4)) → False) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h16 : (p2 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h17 := h13 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41363701308223579739287775304 : ((((((((True ∨ (False ∧ p3)) ∨ p5) ∧ False) ∨ ((p1 ∨ True) ∨ p5)) → (p5 ∧ True)) → ((p1 → (p3 ∧ p3)) ∨ (False → p4))) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321335886750208391564767290757 : (p4 ∨ (p5 ∨ (False ∨ ((((p2 ∨ p3) → p1) ∧ ((p3 → ((True → p1) ∨ ((p2 → ((p2 → (p4 ∨ p2)) ∧ p3)) ∧ False))) → False)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((True → p1) ∨ ((p2 → ((p2 → (p4 ∨ p2)) ∧ p3)) ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p2 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198902190806072806192639549995 : ((p3 → ((p2 ∨ (p2 ∧ p5)) ∧ (True ∧ p2))) ∨ (((p1 ∨ ((False ∨ ((p3 → (p4 ∧ p5)) → (p4 → p5))) → p2)) → p3) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136831738450382741446889205396 : (((p1 ∧ True) ∨ ((((p3 → (p2 ∨ p1)) ∨ p1) ∧ (p4 ∨ ((False ∨ False) → ((p5 ∧ (p3 ∨ p3)) ∧ p5)))) ∧ p1)) ∨ ((p3 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205264808738963826130588163112 : ((((True ∨ p1) → p4) ∨ (p2 → p3)) ∨ ((((p2 → (p4 → False)) → (((False → p4) ∨ p5) → (p5 ∧ ((p2 → True) ∨ p4)))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251343901679568551085513408609 : ((p2 → p3) ∨ (p1 → ((((p5 ∧ p4) ∨ ((p1 ∨ (p2 ∨ ((False → (p2 → p2)) → p5))) ∨ p3)) → p5) ∨ (p4 → (p5 → (p4 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308739452408308459696940424039 : (p2 ∨ ((p3 → ((True → p4) → (False ∨ ((((p1 ∧ (p5 ∧ p1)) ∨ (p4 ∨ (((False ∨ p3) → False) ∧ p1))) ∨ (False ∨ p3)) ∨ True)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114307370342256537893545456239 : (((((False ∧ (p4 ∨ (False ∧ p2))) ∧ (True ∨ p3)) ∨ ((p5 ∧ True) → (p1 → (True → p2)))) ∧ ((True ∧ False) ∨ (p3 ∧ p2))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172303560954388918907803113961 : (((((p4 ∧ p5) ∨ True) ∧ ((p2 ∨ p4) ∨ False)) → (p5 ∨ ((p4 ∧ True) ∧ False))) ∨ (p1 → (True ∧ ((p2 → ((p2 ∨ p1) ∨ True)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39165178060957115186860098461 : ((((p4 ∨ p5) → (((False ∨ ((p2 ∨ ((True ∨ True) → (p2 ∨ (p1 ∨ (p1 ∨ p4))))) ∧ (p4 ∧ True))) ∧ (p1 ∨ False)) ∧ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647111383920339498421631254171 : ((((p3 → (((False ∨ (False → p4)) → p2) → (((p1 ∨ (p3 → p2)) → p5) → ((p2 ∧ (False ∧ p1)) ∧ (p5 → (p1 → True)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58026148849205523806808052813 : (((True ∧ p3) ∧ (((True ∧ p5) → p1) ∨ (p2 → (((p3 → False) ∧ (((p4 ∨ p3) ∧ ((p2 ∨ (p1 ∨ p3)) ∧ p5)) ∨ p2)) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174242718825457994324345181375 : (((p1 ∨ ((((p5 ∨ (p4 → True)) ∨ False) ∨ (p2 ∨ True)) ∨ p2)) → (False ∨ p4)) → ((p3 ∨ p4) ∧ (((p3 ∧ True) ∨ p2) → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((((p5 ∨ (p4 → True)) ∨ False) ∨ (p2 ∨ True)) ∨ p2)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55842242690961569604566381892 : (((p1 ∧ (True ∧ (p1 ∨ p5))) ∧ (p2 ∧ (p3 ∧ ((((p1 → ((True ∧ p3) ∨ p5)) ∧ (p4 → False)) ∨ ((p2 ∨ False) ∨ p3)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259637238229421433793263947227 : ((p1 → False) → ((((p1 ∧ (((p1 → p4) ∧ p2) ∨ p2)) ∨ True) ∨ True) ∧ ((((p5 ∧ (False ∧ p4)) → False) → p5) → ((False → True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ (False ∧ p4)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173942869307448126019328905628 : (((((((False → True) → p3) → p5) → (True → True)) ∨ ((True → p4) ∨ p2)) → p2) → ((False → p1) → (((False ∨ (p4 ∧ False)) ∨ p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((False → True) → p3) → p5) → (True → True)) ∨ ((True → p4) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315034014521388736902806548606 : (p3 ∨ ((p3 → ((((p4 → p5) ∧ p3) → False) ∨ False)) ∨ (((((p4 ∧ p5) → p2) → p1) → ((p5 ∧ p4) → p2)) ∨ (p3 → (p5 → p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663684028074051210984603676523 : ((((p1 ∧ (((((True ∨ ((p4 ∨ (p1 ∨ ((p4 ∨ p1) → p4))) ∧ False)) → p2) → (p1 ∧ (p1 ∧ False))) ∨ True) → False)) → (p2 ∧ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∨ ((p4 ∨ (p1 ∨ ((p4 ∨ p1) → p4))) ∧ False)) → p2) → (p1 ∧ (p1 ∧ False))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197928727972137958984725067909 : (((p2 → (p1 → p5)) → ((True ∧ p3) ∨ p1)) ∨ ((((p5 ∨ True) ∨ (p5 → (p3 ∧ (p2 ∧ p4)))) ∨ ((p2 ∨ p5) ∧ (False → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353190855596925966561332553063 : (p4 → (p4 ∧ ((((p5 → ((p2 → False) ∨ p2)) ∨ (True → (True → p1))) ∧ p4) → (((p1 → p5) ∨ (p2 ∨ ((p5 ∧ p2) → p4))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38715638427406752086006452602 : ((((((p3 ∨ p3) ∨ (p1 ∨ p4)) ∧ p4) → ((((p3 ∨ p1) ∧ (((p3 ∨ p2) ∨ (p2 ∧ p1)) → True)) ∨ False) ∨ (p1 ∧ p5))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589566872802023310235966414945 : (((((((p5 ∧ ((p3 ∨ (p1 → False)) → ((((True ∨ (False → p3)) ∧ p2) ∨ (p3 ∨ True)) ∨ p5))) → (p2 ∨ p1)) → True) → p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65248232964202763871765812737 : ((p3 ∨ (((((((p1 ∧ ((p2 ∧ (p1 ∨ True)) ∧ p2)) ∨ p4) ∧ (p5 → True)) ∨ ((True ∨ p5) ∧ True)) → False) → (False ∧ p4)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257221210994214747785796762436 : ((p2 ∨ p2) → ((p2 → False) → (True ∧ (p2 ∧ (p3 → (p5 ∨ (((((p5 → p2) ∧ p4) ∧ ((True ∧ (False ∨ p1)) ∧ True)) ∧ p4) ∧ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805829116738324859783876781235 : (((p3 → (p5 → ((((p2 ∧ p5) → (p4 → p1)) ∧ ((p2 ∨ p2) ∧ ((((p3 ∨ (p4 ∧ p1)) ∨ (p2 → p5)) ∨ p2) ∧ p3))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



