variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204360021281857844080598321075 : (((p1 ∨ (p5 → (p4 ∨ p2))) ∧ True) ∨ (p2 → ((((p1 ∧ (p3 ∨ (((p1 ∧ p5) → False) ∧ p3))) ∨ (False ∨ p4)) ∧ (p3 ∧ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114780402648370386291962165374 : ((((((p5 ∨ p1) → False) ∨ ((p5 ∨ ((p2 → p5) ∧ False)) ∨ p4)) ∨ p3) ∧ ((p1 → (True ∧ p3)) → ((p5 ∨ p4) ∨ p3))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148941221507828240549790016089 : (((p2 ∨ (p4 → (p2 → False))) → (((p4 → (((p2 → (p2 ∨ True)) ∨ True) ∨ p1)) ∧ (True → p4)) → p3)) ∨ ((p1 → p5) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57102991064766238420338036828 : ((((True ∨ p4) ∧ p2) ∨ (((p3 ∨ True) → ((p4 → p3) → (p4 ∨ (p2 ∧ (p5 → (True ∨ (p4 → (False ∨ True)))))))) ∧ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42190434615815848678600234406 : (((True ∧ ((((p4 ∧ (True ∨ ((p1 ∨ p1) ∧ p3))) → p2) → p2) ∨ (p5 → ((p3 ∨ ((False ∨ True) ∧ p5)) ∨ (p4 → p2))))) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38320321072380870902731413768 : ((((p1 ∧ (((p1 ∧ p3) ∨ False) ∨ (p5 → (((False ∨ (p1 → True)) ∧ p2) → (p3 → False))))) → (False ∧ ((True ∨ False) ∨ p1))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265595897735037021417899490804 : (True ∧ (p1 ∨ (((p2 → (p2 ∧ (((p5 ∧ p3) ∨ (True ∧ p4)) → p5))) ∧ p2) → (((False → p1) → False) ∨ (((False ∧ True) ∧ False) ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773701550927872449878422311955 : (((False ∨ (((True ∨ ((((p4 ∨ p4) → False) ∨ ((True ∨ p3) → p1)) ∨ (((p4 ∨ p3) ∨ (True → p1)) ∨ (p3 ∨ p1)))) ∧ p1) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260255165183984493998056472276 : ((p2 → p3) → ((p3 ∧ p2) ∨ (((p2 → ((p1 → p1) → (p5 ∧ p4))) → p2) ∨ (((p4 ∧ (p1 → p2)) ∧ False) → ((p2 ∨ p4) → False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259731362621781915810658204394 : ((p1 → p2) → ((((p2 ∧ (True ∧ False)) ∧ (p1 ∧ p3)) ∨ ((True ∨ p4) ∧ ((p3 ∧ False) ∨ ((((p4 → False) ∨ p5) ∧ p1) → True)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306205195461382967316323316664 : (p1 ∨ ((p5 → (p4 ∧ True)) ∨ (((p5 ∧ True) → ((p4 → (((True → False) → ((p4 ∧ p1) → p1)) ∧ ((p3 ∨ p2) ∧ p3))) ∨ True)) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639964920305858548487951523050 : (((((True ∨ (True ∨ True)) ∨ ((p3 ∧ (True → p5)) ∧ (False ∨ ((p1 ∨ True) → (True ∧ ((((p5 ∧ p1) → False) ∧ True) ∧ p3)))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116004793877310999205723889967 : ((((True → p3) ∧ (p1 ∨ p1)) → (((False → (((p1 ∧ (p5 ∧ ((True ∨ (p3 → p3)) → p2))) ∧ p4) → False)) → p4) ∨ True)) ∨ (p3 ∧ p3)) := by
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
theorem thm_5_vars_135695659158747789767247571427 : (((((p5 ∧ p4) ∨ ((True → p3) ∧ (False → True))) ∧ (True → (p5 ∨ p4))) ∧ ((p5 ∨ False) ∨ (p1 ∧ (False ∧ p1)))) ∨ ((True → False) → p3)) := by
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
theorem thm_5_vars_265767334698298408938569761924 : (True ∧ (p4 ∨ ((((p3 ∨ p3) ∨ (p3 ∨ (((p1 ∧ p1) ∧ p1) ∨ True))) → ((True → ((p2 ∨ p5) → p1)) ∧ (True → p3))) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_48545923041729189710790868369 : (((((((p2 → ((True → ((True ∧ p4) → p3)) → (p3 ∧ False))) → p2) ∧ (p1 ∨ (p4 → False))) ∨ p2) → p5) ∧ ((p4 ∧ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308569868977980555949811505922 : (p2 ∨ (((((p1 ∨ p5) ∨ p1) ∨ p4) ∧ (((p2 ∨ p5) ∨ p5) ∨ (p3 ∨ (p2 ∨ (True ∨ (False ∨ (False → (False ∨ (p5 ∨ p1))))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314541731954138800248358609311 : (p3 ∨ (((((True ∨ (p5 → ((False → p4) ∨ p2))) → ((p3 ∧ False) → p3)) → p2) ∧ (p4 → True)) ∨ (((p5 → (p5 ∨ True)) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245676387279004614340921737567 : ((p3 ∧ p1) ∨ (((p4 ∧ p1) ∧ p5) ∨ (((((p2 → (p3 ∧ p3)) ∧ p2) ∧ True) → (((False → False) → p1) → (False ∨ (p4 ∨ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84057196893798615880240814003 : (((((p1 → (p3 ∨ ((True ∨ p3) → (False → True)))) → p5) ∧ (p4 ∧ (p5 → p1))) ∧ ((p3 ∨ (True ∨ (False → p1))) ∨ (p3 → p4))) → p1) := by
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
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : (p1 → (p3 ∨ ((True ∨ p3) → (False → True)))) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h11
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h10
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h17 : p5 := by
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : (p1 → (p3 ∨ ((True ∨ p3) → (False → True)))) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- Implications on the right can always be decomposed.
            intro h21
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h18
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h23 := h7 h17
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h25 : p5 := by
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h26 : (p1 → (p3 ∨ ((True ∨ p3) → (False → True)))) := by
            -- Implications on the right can always be decomposed.
            intro h27
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h28
            -- Implications on the right can always be decomposed.
            intro h29
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h30 := h4 h26
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h31 := h7 h25
        -- One of the premise coincides with the conclusion.
        exact h31
  case inr h32 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h33 : p5 := by
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h34 : (p1 → (p3 ∨ ((True ∨ p3) → (False → True)))) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h38 := h4 h34
      -- One of the premise coincides with the conclusion.
      exact h38
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h39 := h7 h33
    -- One of the premise coincides with the conclusion.
    exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115228860881221640898864779999 : ((((p3 → ((p1 ∨ (True → (p2 → p1))) ∧ True)) ∧ p5) ∨ ((((p3 → (False ∧ p4)) ∨ False) ∨ p5) → (p2 → (p3 ∧ p1)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354605964922197540527670019839 : (p5 → ((((((p5 → (True ∨ p1)) → ((p3 ∨ p4) ∧ (p1 ∨ (False → (p2 ∨ p2))))) ∨ (False → (p5 ∧ (False ∧ True)))) → False) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119403851100224491735529606744 : ((p4 → (((p1 ∨ (False → ((p3 → p5) → p5))) ∧ (False ∨ (p5 ∨ ((((p4 ∧ p3) ∧ (True ∧ True)) ∧ p3) ∨ p2)))) ∨ p4)) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160495291601246341677303494255 : (((((True ∨ (p4 ∧ p3)) → (False ∨ (p5 ∨ p5))) ∧ (p5 ∨ p3)) ∧ (p2 ∨ (True → (False ∧ True)))) → (((p2 → False) ∨ (True ∧ True)) ∨ False)) := by
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
    cases h3
    case inl h7 =>
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
    case inr h8 =>
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
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
    case inr h11 =>
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
theorem thm_5_vars_135012245338596664890147544577 : (((p3 ∨ (((p4 ∨ (((p2 ∨ p3) ∧ p1) ∨ ((False ∧ (p5 ∧ p3)) → p4))) ∨ p3) ∨ (p1 → p5))) ∧ (p5 ∧ True)) ∨ (p2 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4164740439618917006692926831 : (p4 ∨ ((((True → p5) ∧ (((p5 ∧ ((p1 ∧ p1) → False)) → (p4 ∧ p5)) ∧ True)) ∧ True) ∨ ((((p1 ∨ p1) ∧ p1) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324419606794912892997398451916 : (p5 ∨ ((p2 ∨ (p3 ∧ ((p2 ∨ True) → p2))) → (((p3 ∨ (p3 → p4)) ∨ (((p4 ∧ p4) ∧ (p5 → ((p4 ∨ p2) ∨ True))) → True)) → p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h10 := h8 h9
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141142387159875521460751777236 : ((((True ∨ (p1 → (False ∨ p4))) → False) ∧ (p4 ∧ ((((p5 ∨ p5) → (p3 ∨ (p3 ∨ p5))) ∨ (True ∧ p2)) ∨ False))) → ((True → p3) → p1)) := by
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
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ (p1 → (False ∨ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (True ∨ (p1 → (False ∨ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773495709713031005917123967185 : (((False ∨ (((p3 ∨ ((p3 ∨ ((p5 ∧ p1) ∨ ((p1 → ((p2 ∧ p1) ∧ True)) ∨ p5))) ∨ (p4 → (False ∧ False)))) ∨ (False ∨ False)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_45104134474477099495302305351 : ((((p1 ∨ p2) → (((p5 ∨ ((p4 → ((((p5 ∨ p3) ∨ True) → (False ∧ (True ∨ True))) ∨ True)) ∧ (p1 → True))) ∨ p4) ∨ p5)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18987576614475852869721651262 : ((((((((p2 → True) → ((p3 ∨ True) → True)) ∨ (True ∧ (p1 ∨ p3))) ∨ False) ∨ True) ∧ True) → (False ∨ (p5 ∨ (False → (p5 ∨ p1))))) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81823269431471799001624362009 : ((((True → ((p5 ∨ (((p2 ∨ (True → True)) → (p4 ∨ p5)) ∨ ((p4 ∨ (True ∨ p2)) ∨ p1))) ∨ p5)) ∨ False) → ((False ∧ p2) ∧ True)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((p5 ∨ (((p2 ∨ (True → True)) → (p4 ∨ p5)) ∨ ((p4 ∨ (True ∨ p2)) ∨ p1))) ∨ p5)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328286015146300491906268174420 : (True → (((p3 ∨ (((True ∧ p3) ∧ (p5 ∨ (p1 ∨ p5))) ∧ (((p4 → p3) ∧ p2) ∨ p1))) → (p2 ∨ p2)) ∨ ((p3 → p3) → (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167629199730740070217505323020 : ((((p5 ∧ (((True ∧ (p5 ∧ True)) ∧ p4) → (p5 ∧ (p4 → p3)))) → p4) → (p3 ∧ False)) → ((p2 ∨ (p5 ∨ ((True → p5) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40354865124777560976196050319 : (((((((p4 ∨ (p3 ∨ (p4 ∧ p2))) ∨ (p5 ∧ (((p1 → (p3 ∨ ((p3 → p2) ∧ p1))) ∧ p4) ∨ p1))) → False) → p2) ∨ p2) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_543159626978916438861603344 : ((((p3 ∨ ((((True ∨ (p1 ∨ p2)) ∨ (p5 ∧ p5)) ∨ p3) ∧ ((p3 ∧ False) ∨ p2))) → ((p3 ∨ p4) ∨ (False → p3))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54541141057305888716234569562 : ((((p2 → p4) → (True ∧ ((p5 ∨ p2) ∧ False))) ∨ ((True → True) ∧ (((p5 ∧ p5) ∧ ((((p2 → False) ∧ p3) ∧ False) ∧ p4)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257219688091893157820222937415 : ((p2 ∨ p2) → ((p2 → p5) ∨ ((False ∧ (((False ∨ p3) ∨ p2) ∧ p5)) ∨ ((True ∨ (((p5 ∧ (p2 ∨ p2)) ∧ p1) ∧ (p2 → p2))) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_251427358689766462920026653944 : ((p2 → p5) ∨ (((((p4 ∧ (p3 ∧ p5)) ∨ (p1 ∨ ((True ∧ ((True ∧ False) → p1)) ∧ p4))) → False) ∨ ((p1 → p5) ∧ p5)) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184999553188856272684502539449 : (((p3 ∧ p2) ∧ (p4 ∨ (p1 → ((p4 ∧ (p2 ∨ p1)) ∨ p4)))) ∨ ((p1 → True) ∧ (((((p3 ∨ False) ∨ False) → p1) → True) ∧ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160066151805028519127488677285 : (((p4 ∧ ((p1 ∨ ((p2 → ((p5 ∧ (p2 → p4)) ∧ p5)) ∧ ((p5 ∧ p5) → p4))) ∧ p1)) → True) → (p4 → (p3 ∨ ((p5 ∧ p5) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343426403378500062240841394442 : (p2 → ((p1 ∨ False) ∨ (((((p2 → (p4 ∨ ((True → (p4 ∧ True)) ∧ (True ∧ True)))) → (p5 ∧ (p5 → (p5 → p1)))) ∧ False) ∨ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656635725689665808174205270601 : ((((((p4 → ((False ∨ True) → True)) ∨ (p4 ∧ p3)) → (((False ∨ (p3 → p5)) → p1) ∧ (p3 ∨ ((p5 → p5) ∧ p3)))) ∨ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52546131379377041062190912823 : ((((((p3 → (((False ∨ p5) ∧ True) → (p1 ∨ p1))) ∨ p3) → p4) → False) ∨ (True ∨ ((True → (p2 ∧ ((True → p5) → p3))) ∧ False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40937905075090811646254047622 : (((((True ∧ (((((p1 ∧ (p1 ∧ ((p2 → False) → (p3 → p1)))) ∨ p5) → True) ∨ (p3 ∧ False)) → p5)) ∨ p4) ∨ (p2 → True)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18045872166797924759992247741 : (((False ∧ ((((p2 → ((p2 ∨ ((p1 → p1) ∧ (p2 ∨ p5))) ∧ (p5 ∨ p5))) ∨ p3) ∧ p2) ∨ p2)) ∨ (p3 → (True ∧ (p3 ∧ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64677322402139357357137107018 : ((p1 ∨ (p3 ∨ ((((p3 → True) → p1) ∨ (p2 ∧ (True ∧ (p5 ∧ ((p2 → p5) → p3))))) ∧ ((p5 → (True ∧ p3)) ∧ (p5 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46334106362276901159682691322 : ((((p3 → (((p3 ∧ (p1 ∨ ((True → (True ∧ False)) ∧ False))) → (p5 ∨ False)) ∨ p3)) → (((p4 ∨ p2) → True) → False)) ∧ (p5 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351623056811139724905708716566 : (p4 → (((((p4 ∧ (p3 → p3)) ∨ (False ∨ (p2 → ((p5 ∨ False) ∧ False)))) → p2) ∧ p2) ∨ ((((p4 → (p4 ∨ p3)) → p3) ∧ p1) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764241355423203243638136514297 : (((p4 ∧ (((((True ∨ p3) → (p3 ∨ (p1 → (False ∨ p5)))) → (p4 → (False ∧ (p4 → (p4 ∨ (p3 ∧ (True → p4))))))) ∨ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135401807859005190695558788512 : (((((p1 ∨ ((p2 ∧ False) → False)) ∧ (p4 ∧ p5)) ∨ (p2 ∨ (((p4 → p5) ∧ True) ∨ True))) ∨ ((p1 → p5) ∨ p4)) ∨ (False ∨ (p3 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171507456686666081644067688796 : ((((((p3 → ((p4 → True) → (p2 ∨ p3))) ∨ (p4 ∧ p3)) → True) ∧ p1) ∨ p3) ∨ (p1 → (((p1 ∧ True) → (p2 ∨ p3)) ∨ (p5 ∨ p1)))) := by
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
theorem thm_5_vars_65420956883413541264090309261 : ((p3 ∨ ((False ∧ (p1 ∧ p4)) ∨ ((p5 ∧ p4) → (((((p4 ∧ False) ∧ p1) ∨ p2) ∨ False) ∨ ((True ∨ ((p5 ∨ False) ∧ p1)) → True))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654461460908780436492609031731 : ((((((False ∧ p3) ∨ (((False ∨ p5) ∨ (((p3 ∨ p3) ∧ p3) → (p5 ∧ ((False → (p1 → p5)) ∨ True)))) ∧ True)) ∨ True) ∨ (p3 ∨ False)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_766218615977174911772017802586 : (((p4 ∧ ((p4 ∧ p5) ∨ (((True → (False → (False ∨ (((p1 → p1) ∧ p2) → (((p5 ∧ p1) ∧ p5) → (p1 → p2)))))) → p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299342449409329024135057312797 : (False ∨ (((p4 → (p3 → p3)) ∧ (p4 → (((p1 ∨ p5) → ((p4 ∨ (p3 → p4)) ∨ False)) → (p3 ∧ ((True ∧ (p3 ∧ p4)) ∨ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40623110522842820610155873376 : (((((p2 → (False → ((((p4 ∧ False) → p1) ∨ ((p5 ∨ p3) → p5)) ∨ (p5 → (p3 ∧ ((True ∧ True) ∨ p4)))))) ∨ p3) → p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343587006404266486193243365663 : (p2 → ((p1 → p3) → (p1 → (((p5 ∧ (((p4 ∨ ((p1 ∨ (p1 ∨ (p2 → True))) → p1)) ∨ p5) → False)) ∨ (p5 ∧ p1)) ∨ (False → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46191156113284662266560628806 : ((((False ∨ (((((p2 ∧ ((p5 ∨ (((False ∨ (False ∨ p4)) ∨ p1) ∧ p1)) ∨ p3)) → p5) ∨ p5) → False) ∧ p1)) → p4) ∧ (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111661246285101112740912894320 : ((((p5 ∧ ((p3 ∧ ((True → (((p3 → ((p2 → True) ∨ p2)) ∨ p5) ∨ True)) → (p4 → (False ∧ p2)))) ∧ p2)) ∨ True) ∨ p5) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2371540284616900733626199294 : (((p2 → ((p2 → p4) ∧ (True → p4))) ∨ ((p4 ∨ p5) → p3)) ∨ ((p1 → (p2 ∨ ((True → ((p4 → p5) → p5)) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350052569159880795973698428885 : (p4 → (((p5 → ((p2 → p5) → ((p5 ∨ p1) ∨ (p3 ∨ (p5 → ((p2 ∧ (p2 ∨ ((p4 ∧ p5) → p3))) → (False ∧ p5))))))) → False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68514433698387829495399102752 : ((p3 → (p5 ∨ ((p3 ∧ (((p3 ∨ True) → ((p3 ∧ (p4 → p4)) ∧ (p5 ∨ (False → True)))) ∧ False)) ∨ (True → (p5 ∨ (False ∨ True)))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59938809911186184518801518824 : (((True ∨ False) → (p1 ∧ (p3 ∨ ((p2 → (((p1 → (p3 ∧ ((p2 ∧ (True → p4)) ∨ (p1 ∨ (True ∨ p4))))) ∨ p2) ∧ p1)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158424593825541684842892570954 : (((p5 ∧ False) ∨ ((((True ∧ (p2 → p4)) ∧ ((p4 ∧ (True ∨ True)) ∨ True)) → p2) ∨ (p2 ∧ p2))) ∨ (p1 ∨ (True ∨ (p5 ∨ (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654156240542615266417078588870 : ((((((((True ∨ False) → ((p3 ∨ (p5 ∨ (((p5 ∧ p5) ∨ True) → p3))) → ((p4 ∧ False) ∨ p4))) ∧ p4) ∨ True) ∨ p5) ∨ (False → p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792373406736217297727434119806 : (((True → (((p5 ∨ ((p1 ∨ (p2 → (p2 → p4))) ∧ p1)) ∧ (p3 ∧ (p2 → False))) ∨ ((p4 ∧ (p4 → ((p1 ∨ False) ∧ p4))) → p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168712969701196262675610627748 : ((True ∨ ((((p4 ∧ p2) → p4) ∧ True) ∨ ((((p4 ∧ p2) ∧ p1) ∧ (p4 ∧ p2)) ∧ p5))) → (p1 → ((p5 ∨ False) → (False ∨ (p4 ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
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
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h14.left
        let h20 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193989273286662053894348333774 : ((p3 ∨ (p2 ∧ (p1 → (p2 → (True → (p4 ∨ p5)))))) → ((p2 ∨ (((((p4 → p5) ∧ (p5 → p4)) ∧ True) ∧ True) ∨ (p5 ∧ p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112799504518378711939277174033 : ((((p5 → (p3 → (False → (p2 → False)))) ∧ ((p5 ∧ p3) → (p4 ∧ (((p5 ∧ p5) ∨ (p3 → (p2 ∨ p5))) ∧ True)))) → p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113087308483960790791345417777 : (((p4 ∨ (p4 → (p5 ∨ ((p1 ∨ p5) ∧ (p4 ∧ ((((p1 ∨ (p5 ∨ p5)) → p1) ∧ p4) ∧ ((p5 ∨ p3) ∧ p5))))))) → p1) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72633056073120115505103894404 : ((((True → (((p2 ∨ True) ∨ ((p1 ∧ ((p2 → (p1 → (True → p5))) ∨ (p2 ∨ (p4 ∧ p2)))) → (p4 ∨ False))) ∧ p2)) ∧ p4) ∨ False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146925808105795589758404249112 : ((((p5 ∧ ((p3 ∨ (False → (False ∨ p2))) → (p3 ∨ (p2 ∨ ((p3 ∧ (p2 → p1)) ∨ p4))))) ∧ p5) ∧ False) ∨ (True → (True ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232251244093785236664489568015 : (((p1 → p5) → p4) → (((p2 ∧ (p2 → ((p4 → p3) ∨ (p3 → ((False ∨ p2) ∧ p2))))) → (p5 → (p4 → (p2 → p3)))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40725921264347365448067034215 : ((((((p5 ∨ (p4 ∨ (p5 → p1))) ∨ p5) → (((p2 → (False ∧ (False ∨ p4))) → ((p3 → p3) → p2)) ∨ (p1 ∨ False))) → p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241602725901807774790497107120 : ((False → p4) ∧ ((((((True ∨ True) → p3) ∧ p4) → p5) ∨ p2) → ((((p3 ∨ (False ∧ (p4 ∨ False))) ∨ (p1 ∧ (p5 → False))) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_108272729318612891690730284201 : ((True ∧ ((p4 → ((p3 ∨ ((p3 ∨ p3) ∨ ((p5 → p2) → p3))) ∨ p3)) ∨ (p5 → (p3 ∨ (p1 ∨ (p1 → (p5 ∨ True))))))) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58427418131495543992948686425 : (((p2 ∨ p4) ∧ (p4 → ((((p5 ∧ ((p1 → (p3 ∨ p5)) ∨ p2)) → p1) → (p3 ∧ (True ∨ ((p3 ∧ False) ∧ (True ∧ p3))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317937367259221314542929196095 : (p4 ∨ ((p2 ∨ (((p2 ∨ (((p2 ∨ p2) → p2) → p2)) ∨ ((p2 ∨ (p2 ∧ p3)) → (((p1 ∨ False) ∧ (p5 → p5)) ∨ p4))) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_744896950517346913766484389868 : ((((p3 ∧ p5) → ((p3 → (((True ∧ p4) → p3) ∧ False)) ∧ ((p2 ∨ (p5 ∨ True)) ∧ (((((p5 ∧ p5) ∧ False) → True) → False) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116793241766794755751697735464 : (((p2 ∨ False) ∨ ((False → p5) ∧ ((((p3 → p5) → p3) ∧ (p4 ∧ ((p5 → True) ∧ (p2 → ((p5 → False) ∧ False))))) ∨ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117333085578283040217553697843 : ((False ∧ ((p2 ∨ (p1 → p3)) ∧ (((p4 → p3) ∨ p5) → (((p2 ∨ False) ∨ (p2 → ((False ∧ p4) ∨ (p1 → p1)))) ∨ p3)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316617315977790032442358731313 : (p3 ∨ (p4 ∨ ((p4 ∧ ((((p3 → True) ∨ (p5 ∧ (p3 → p2))) ∧ ((p3 ∧ False) ∨ (((p5 → (False ∨ p5)) ∨ p4) ∨ p2))) → p3)) → p3))) := by
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
  have h4 : (((p3 → True) ∨ (p5 ∧ (p3 → p2))) ∧ ((p3 ∧ False) ∨ (((p5 → (False ∨ p5)) ∨ p4) ∨ p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184015594031622745801723488485 : ((((False ∧ ((False → p4) → (p1 ∨ (p4 → p2)))) ∨ p2) ∨ True) ∨ ((p1 → True) ∨ ((p3 ∨ (p3 → p4)) ∨ (True ∨ ((p3 ∨ p1) ∧ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114506144958691314463332309997 : ((((p5 → (True ∨ p5)) ∨ ((p5 → ((p1 ∨ (p2 → False)) → (p4 ∨ (p5 ∨ False)))) ∧ p2)) → (False ∧ ((p4 ∧ False) ∨ p4))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56569412438287525939707133582 : (((True → ((p1 ∨ p2) ∨ p5)) → ((p2 → ((((((False ∧ False) ∧ p1) → p3) → p2) ∧ (p4 ∨ p5)) → ((p1 ∨ p5) → False))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130483979082981461526112021537 : (((((((False → p4) → p2) ∨ (((p4 → p3) ∧ p2) → p5)) ∨ ((p3 → p3) → p1)) ∧ p5) → (p1 → (p2 ∨ p5))) ∧ (p3 → (p5 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226361039953129139872400507202 : (((True → p1) ∨ False) ∨ (False ∨ ((((p2 → p2) ∧ p3) ∧ p1) → (((((p3 ∨ p3) ∨ p4) ∧ p3) ∨ ((True → p1) ∨ p3)) → (p4 ∨ p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h1.left
      let h30 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670874231773959573812411626331 : ((((p3 ∧ ((((p1 ∨ p5) ∧ ((p1 ∧ ((((False ∨ p3) ∧ p4) → p2) → p1)) ∨ (p2 ∧ p2))) ∨ p3) ∧ p2)) ∨ (p3 → (True ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350143329353678011614738450038 : (p4 → (((False ∧ ((((p1 → True) ∧ p4) ∨ False) → ((p2 ∧ p5) ∧ p2))) ∨ (True ∧ (((True ∨ p5) ∨ (p2 ∨ (p1 ∨ p4))) ∨ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354033957859178747530671620456 : (p4 → (p4 → ((((p5 → (False ∨ ((p4 ∨ p2) → (True ∨ ((p4 ∨ p2) → p2))))) → p5) → (p1 ∧ (p2 ∧ p2))) ∨ (p4 ∨ (p4 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139635298692662330155394945466 : ((((((True ∨ p5) → (p2 ∧ (p4 ∧ p5))) ∧ True) → (((((p3 ∨ p5) → (p4 → p3)) ∨ p3) → p3) → p5)) → p1) → ((p2 ∧ p1) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203447698668963366045459236683 : ((True ∨ (((p3 ∧ p3) ∧ p2) ∧ p3)) ∧ ((((((p3 → p1) ∨ ((p1 → False) ∧ (p1 → True))) ∧ p4) → ((False → p2) → p3)) ∨ True) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597505044616969428904137752845 : (((((p3 ∧ ((False → p1) ∧ p4)) ∨ (p4 → (p4 ∧ ((p4 ∧ (((p5 → (p5 ∨ p2)) ∧ p1) → p2)) → ((False → p2) → p5))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58516905901621636689139388518 : (((p5 ∨ True) ∧ (p4 ∨ (p5 ∧ ((((p2 ∧ p3) ∧ p3) ∨ p5) ∨ (((True ∨ ((p2 ∧ ((p2 ∧ p1) → p4)) → p5)) ∨ p4) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311889054194118201217400214879 : (p2 ∨ (p2 ∨ (((p2 → True) ∨ (False ∧ ((p4 → p1) ∧ False))) ∧ ((True ∧ ((p4 ∨ p4) ∧ ((p2 ∨ (p3 → True)) → p3))) → (p1 → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ (p3 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ (p3 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h15 := h7 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37908686809286524223925948806 : ((((((p5 ∨ ((p2 ∧ p1) ∧ p2)) → ((p3 ∧ p2) → (True → True))) → ((False → (p3 → p3)) ∧ (p5 ∧ False))) ∧ (True ∨ True)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614747251783035798446700045820 : ((((((p4 ∧ ((p4 ∧ ((((True ∧ p1) ∧ True) → p3) ∧ p2)) ∨ p2)) → ((p5 ∧ True) ∨ p5)) ∨ ((True → (p3 → p1)) ∨ True)) ∨ False) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324286822474050936939557095677 : (p5 ∨ (((((p5 ∧ p2) ∧ True) → (p2 ∨ p4)) ∨ p3) → (((p4 ∨ p5) ∨ (p2 ∨ p3)) ∨ (p4 ∨ ((((p4 → True) ∨ True) ∨ p3) ∧ True))))) := by
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
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156958647138092644271450227720 : (((((p4 → p2) → ((((p5 → (p5 → False)) → p2) ∨ p3) ∨ p1)) ∨ ((p4 ∧ p4) ∨ True)) ∨ p1) ∨ ((p2 ∨ ((p3 → p2) ∨ False)) ∨ p4)) := by
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



