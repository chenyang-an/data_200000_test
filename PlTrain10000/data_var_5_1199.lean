variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42299683888977216585957150651 : (((p2 ∧ ((False → (False ∨ (p5 → (p4 ∨ (True ∧ (p3 ∧ (((False ∨ p3) → (p5 ∨ (p4 ∨ p3))) ∧ (p1 ∧ False)))))))) → p1)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55871973474401657556398419672 : (((True ∨ ((True → p4) ∨ p1)) ∧ (p3 → ((((p5 ∧ p4) ∧ ((((p3 ∨ p4) ∨ p5) → False) ∧ p4)) → p1) → (p4 → (p5 ∨ p4))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301533653122109326540609031622 : (False ∨ (((p2 ∨ p1) ∨ False) ∨ ((((p4 → p2) ∨ ((((False ∨ p3) ∨ p4) ∧ p5) ∨ (p2 → p2))) → p3) → (p3 ∨ ((p4 ∧ p4) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → p2) ∨ ((((False ∨ p3) ∨ p4) ∧ p5) ∨ (p2 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318724956156820062285393005986 : (p4 ∨ (((p4 ∨ (p5 ∨ (p2 ∨ (p1 → p5)))) ∨ (((p2 ∨ ((p4 → (True ∨ p4)) ∨ True)) → ((p4 ∨ True) ∧ True)) ∧ p4)) → (p1 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115045345929410050587667080891 : ((((p2 ∨ ((p1 ∨ (True ∨ (False → p2))) ∧ (p3 ∨ p4))) ∨ p2) ∨ (((p1 → (p2 ∨ (p1 ∧ p4))) → p3) → (p4 ∨ True))) ∨ (p4 ∨ p1)) := by
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
theorem thm_5_vars_111770367078870575310011770036 : ((((p2 ∧ (((False ∨ (p3 ∨ ((p1 ∧ False) ∨ ((p5 ∨ p4) ∨ (p1 ∧ p2))))) → (p5 ∧ p3)) ∧ p2)) ∧ (p4 → True)) ∨ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340920671539731098496890872120 : (p2 → (((((p5 → (p3 → p4)) → p1) → p1) ∧ ((p4 → (p2 ∨ ((True ∨ p1) ∨ True))) → ((False ∧ p3) ∧ ((p4 ∧ False) → p5)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27382702880613237069272112277 : (((p1 ∧ p1) → ((((((p4 ∧ (p5 ∨ (p4 ∨ p3))) ∧ (((True ∨ True) → p2) → (True ∨ False))) ∨ p1) ∧ p3) ∧ (p4 → p1)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165706330186807554234958733608 : (((((True → p5) → p1) ∨ p4) ∧ ((p1 ∧ ((((p3 ∨ True) ∨ p5) ∧ p3) ∨ p4)) → p3)) ∨ (((False → p1) → (False ∧ (True → True))) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46996226785839643634641760938 : ((((((((p4 ∨ p4) → p5) → p1) ∧ p2) → (((p3 ∧ p1) ∧ True) → ((((p5 → p3) → p2) ∧ p1) ∨ p1))) → p5) ∨ (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310133023276595362237035852326 : (p2 ∨ ((p4 ∧ (((p1 ∨ p4) → ((p5 ∨ (p3 ∨ p3)) ∧ True)) ∧ (p2 ∧ p2))) ∨ (p5 → ((p2 ∨ ((True ∧ (p3 ∧ p1)) → True)) ∨ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654405475357078053438158812840 : (((((((True ∨ p4) → (p4 ∧ p2)) ∧ ((p1 → ((p4 → ((False ∨ (True → p5)) ∨ (False ∧ p2))) ∧ p4)) → p3)) ∨ False) ∨ (p3 → p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594737728607874103750903217526 : ((((((True → p4) → (p2 ∧ (p5 → (p3 ∧ ((p1 → (p4 → (p1 ∨ p3))) ∨ p4))))) → (p5 → (((p3 ∨ p1) ∨ p4) → False))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308511600004397807006552809489 : (p2 ∨ ((((((p4 ∨ (p5 ∨ p2)) ∧ ((False → p3) ∨ True)) ∨ (p3 ∨ p5)) ∨ (False → False)) ∧ ((p4 → True) ∨ ((p2 → p4) ∨ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179024696231080778188666065804 : (((p1 ∨ p5) → (((((p1 → p3) ∨ False) ∧ p2) → (True ∧ p3)) → False)) ∨ (p4 ∨ (p5 → ((p4 ∨ ((True → p1) ∨ False)) ∨ (p5 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114254246957859575771537683619 : (((p1 → ((((p2 ∧ ((False ∧ (p5 ∧ True)) → p1)) → False) ∧ (False → p2)) ∨ ((p5 ∧ False) → p3))) → (p3 → (p3 → p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227690269183321565663999071278 : ((p1 ∧ (True ∧ p3)) ∨ ((((p5 ∨ p4) ∧ p5) ∨ (p2 → True)) ∧ (True ∨ (p5 ∨ ((p5 ∧ p1) ∨ (False → (p1 ∧ ((True ∨ p4) → p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_113326832420823830326098153979 : ((((p4 ∨ p5) ∧ ((True ∧ (p4 ∨ False)) → (((p4 ∧ (p3 ∨ ((p2 ∨ (False ∨ p3)) ∨ True))) → True) → p4))) ∧ (p2 ∨ p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323480918783924036070389005230 : (p5 ∨ (((((p3 ∧ (True → (p4 ∧ True))) ∧ (p1 → ((p2 ∨ ((False ∧ p2) ∧ True)) ∨ (p2 ∧ p5)))) → p5) → p3) ∨ ((p3 ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650835170511680744435786875501 : ((((((p2 → ((p4 ∨ p4) ∧ (True → p4))) ∧ p2) → (p1 ∨ (p4 ∧ ((True ∨ ((p4 → p4) ∧ (p3 → p5))) → True)))) ∧ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47779672434768013789152479803 : ((((p5 → ((((((p4 ∨ p2) ∧ (True → p1)) ∨ p5) ∨ (p1 ∨ ((True ∧ p1) ∨ True))) ∧ (p1 ∨ False)) ∧ p4)) ∨ True) → (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61671215968259126953847194659 : ((p1 ∧ (p5 ∧ ((((p1 ∧ ((True ∧ p5) ∧ True)) ∨ (p1 ∨ (p5 ∨ False))) ∧ (p4 ∨ ((True ∧ p2) ∧ (True ∨ (p4 ∧ p3))))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166315439082006192678338634422 : ((p5 ∧ ((((p5 ∨ (p3 ∧ (p3 ∨ ((p5 ∨ p3) ∧ (p4 ∨ True))))) ∧ p5) → p4) → p5)) ∨ ((((True → p3) → (p3 ∧ True)) → True) ∧ True)) := by
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
theorem thm_5_vars_86020159548505932668099279172 : ((((p3 ∨ p4) ∧ ((p2 → (p5 ∧ (False ∧ True))) ∨ p1)) ∧ ((True → False) ∧ ((p5 ∨ ((True → (p3 → p2)) ∧ (p1 ∨ p4))) ∨ p1))) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
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
      let h19 := h3.left
      let h20 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
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
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h3.left
      let h32 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h36 := h31 h35
          -- False on the left can always be used.
          apply False.elim h36
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h41 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h42 := h31 h41
            -- False on the left can always be used.
            apply False.elim h42
          case inr h43 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h44 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h45 := h31 h44
            -- False on the left can always be used.
            apply False.elim h45
      case inr h46 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h47 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h48 := h31 h47
        -- False on the left can always be used.
        apply False.elim h48
    case inr h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h3.left
      let h51 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h53 =>
          -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
          have h54 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h50, we can now drive its conclusion.
          let h55 := h50 h54
          -- False on the left can always be used.
          apply False.elim h55
        case inr h56 =>
          -- Conjunctions on the left can always be decomposed.
          let h57 := h56.left
          let h58 := h56.right
          -- Disjunctions on the left can always be decomposed.
          cases h58
          case inl h59 =>
            -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
            have h60 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h50, we can now drive its conclusion.
            let h61 := h50 h60
            -- False on the left can always be used.
            apply False.elim h61
          case inr h62 =>
            -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
            have h63 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h50, we can now drive its conclusion.
            let h64 := h50 h63
            -- False on the left can always be used.
            apply False.elim h64
      case inr h65 =>
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h66 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h67 := h50 h66
        -- False on the left can always be used.
        apply False.elim h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118649891989243525530364232806 : ((p4 ∨ (p1 ∧ (p3 ∨ (p2 ∨ (((p1 → (False ∨ True)) → (((p4 → p3) ∧ p1) ∧ ((True ∧ p3) ∧ (p4 ∨ p1)))) ∧ p3))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330478262995045839884296827290 : (True → (p4 ∨ (((p5 → (((((((True ∧ p5) → ((False → p4) ∧ False)) ∧ p1) ∨ p1) → p4) → p1) ∨ (p3 → p5))) ∨ (p5 ∧ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309929470241276802300521165466 : (p2 ∨ (((p4 ∧ (p1 ∨ p5)) ∧ ((((p4 ∧ p3) ∧ ((True ∨ True) → p5)) ∨ p5) ∧ (False ∧ p1))) ∨ ((p2 ∧ p2) ∨ (p3 → (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64670475525983100339462804705 : ((p1 ∨ (p2 ∨ (((p4 ∧ (p2 ∧ ((p3 ∨ (p3 ∧ (p4 ∨ True))) → ((p4 ∧ (False → p1)) ∧ True)))) → (False → (True ∧ p1))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326952906396836302835231198212 : (True → ((((((True → p2) ∧ ((p4 ∨ (p3 ∧ (p2 ∨ p4))) ∨ (True ∧ p4))) ∧ (p4 → p1)) → ((False ∨ p3) ∧ True)) ∨ (p5 → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114939872466140941888110468611 : (((((p4 → p5) → (False ∧ p5)) → ((p1 → (p2 ∨ p1)) ∨ (True → True))) → (p3 ∧ (False ∨ ((True → (False → p1)) ∧ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204300970476076770155645237658 : (((True ∧ (True ∧ (p1 ∨ p3))) ∧ p4) ∨ (p5 ∨ ((p2 ∨ (False → (((p5 ∨ p3) ∧ (p3 ∧ p1)) ∧ p5))) ∧ ((True ∨ (p1 → p3)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650810874305447424615573047801 : ((((((p4 → p4) ∧ ((True ∧ p3) ∨ (p2 ∧ p5))) ∨ ((p5 ∨ False) ∧ (((p3 ∨ True) ∧ False) → ((p1 → False) ∨ True)))) ∧ (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113586911200137092797656023958 : (((p3 ∧ (((True ∧ p5) → (((True → p5) ∧ (True ∨ p2)) → (p4 ∨ p2))) ∧ (False → (True ∧ (True ∨ p5))))) ∨ (p3 ∧ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676136362535475720057618514971 : ((((((p5 ∧ (p1 ∧ p1)) ∧ p3) ∨ (((p1 ∨ (p4 → ((False ∨ p4) ∨ p4))) ∨ True) ∧ (p1 ∨ p4))) ∧ (((p4 ∨ p2) → p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192771217752913283288782568059 : (((p3 ∧ (p2 ∨ (p2 ∧ ((p5 ∧ False) ∨ p2)))) → False) → (((p5 ∨ p4) ∧ (((p1 ∧ ((p1 → p4) → p2)) ∨ p5) ∧ (p1 ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908383707995920473353119940885 : (((((p1 ∧ ((p3 ∧ p4) ∨ (True → ((p3 ∧ (True → ((p2 ∧ p5) ∧ True))) ∧ p4)))) ∧ p2) ∧ (p5 ∧ (p3 → ((p2 ∨ p3) ∨ p4)))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662554654910474858539312576460 : (((((((False ∧ (True ∧ False)) ∨ p5) ∧ p4) → (((p3 ∨ p4) ∨ (p3 ∧ ((True ∧ False) → False))) ∨ (p5 ∨ (False → p2)))) → (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259785090819997577956243987883 : ((p1 → p2) → (p1 → ((((((p5 → ((p5 → (p5 ∨ p3)) → (False ∨ (p1 → False)))) → p4) → p2) ∨ (p2 ∨ p3)) ∨ (p3 → p5)) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138242225277545168416112514280 : ((p2 → (((p2 → True) → (p2 → p4)) ∧ (p1 ∧ (((p4 ∧ p1) ∧ (((True → (p1 ∨ p2)) ∧ p1) → True)) → p5)))) ∨ (p3 → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122886464462289600613111692184 : ((((p2 → p1) ∨ (p3 ∧ ((((((p3 ∨ True) → False) → p4) → p2) ∨ (p3 → (False ∨ p5))) → True))) ∧ ((False → p5) ∨ False)) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319156469528087250869540882918 : (p4 ∨ (((p3 ∧ ((((p1 ∧ p2) ∧ (p5 ∧ p2)) ∧ p1) ∨ (p4 ∧ (p3 ∨ (True ∨ p2))))) ∧ p1) ∨ ((p3 ∨ p3) → ((p3 ∨ False) ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587441152987841633185018736037 : (((((((p5 ∧ (((p1 → p1) → (((p5 → (True → p4)) → ((p4 → p1) ∧ (p3 → p5))) ∧ True)) → True)) → p2) ∨ p4) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41227426356918507983960288011 : ((((((p2 ∧ False) → (p1 → p3)) ∧ (((((True → p1) → p5) ∨ True) ∧ p1) ∧ (False ∧ False))) ∧ (((p1 ∧ p1) ∧ True) ∨ False)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798017684986311528053594805407 : (((p1 → (((False ∧ (True ∧ (p5 ∨ p4))) ∧ (((False ∨ p2) ∨ ((p4 ∨ ((p4 → p4) → p3)) → p2)) ∨ False)) ∧ ((p4 → p5) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112246470301431580818100424412 : (((p3 ∨ ((p1 ∧ True) → (p3 ∧ (((p1 ∧ ((p4 ∧ (False → (p4 ∧ False))) ∨ (True ∧ (p5 ∨ p1)))) ∧ True) ∨ p4)))) ∨ p3) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202087910896354278930352096879 : ((((p5 ∨ (p2 ∨ p4)) ∨ p5) → True) ∧ (((((False ∨ p1) ∧ False) ∧ p4) ∨ ((p4 ∧ (p5 ∨ False)) ∧ (((p1 → p5) → p4) ∨ p5))) ∨ True)) := by
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
theorem thm_5_vars_113186551809069002791031578330 : ((((((True ∨ (p5 ∧ p3)) → (p5 ∧ (p4 ∧ p4))) ∨ (True ∧ (p2 → (((p4 ∧ p4) → p1) ∨ p1)))) ∧ False) ∧ (True ∧ p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259924928249252316364809273322 : ((p1 → p5) → (((p2 ∨ ((p4 ∧ False) ∨ p5)) ∧ (((((((False → False) ∧ p1) ∧ True) → (True ∧ False)) ∧ p1) ∧ True) ∧ (p5 ∨ p2))) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : (((False → False) ∧ p1) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
        -- One of the premise coincides with the conclusion.
        exact h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h15 := h10 h13
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h18 : (((False → False) ∧ p1) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
        -- One of the premise coincides with the conclusion.
        exact h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h18
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h4.left
      let h28 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h33 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h34 : (((False → False) ∧ p1) ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h35
          -- False on the left can always be used.
          apply False.elim h35
          -- One of the premise coincides with the conclusion.
          exact h32
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h36 := h31 h34
        -- We need to get the right conjuct of h36 based on <expert-advice>.
        let h37 := h36.right
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h39 : (((False → False) ∧ p1) ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h40
          -- False on the left can always be used.
          apply False.elim h40
          -- One of the premise coincides with the conclusion.
          exact h32
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h41 := h31 h39
        -- We need to get the right conjuct of h41 based on <expert-advice>.
        let h42 := h41.right
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249738410225164775128609732784 : ((p5 ∨ p5) ∨ (((p4 ∨ (True ∧ ((True ∨ p5) ∨ p2))) ∨ (p3 → p3)) ∧ (p4 ∨ ((False ∨ True) ∨ (p2 ∧ ((p1 → False) → (True ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38925444859820876150655248240 : (((((False → p3) ∧ p3) → ((p2 ∨ (((p3 → (False ∧ p1)) ∧ False) ∨ p5)) ∧ ((True ∨ p1) ∨ (((False ∧ True) → p4) → p2)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219031470665511964385916990393 : ((p5 ∧ ((p1 ∧ p2) ∨ p1)) → ((False ∨ (p5 ∧ p5)) ∧ (((p3 ∧ ((p3 ∨ p4) → (False ∨ (True → False)))) ∨ p1) ∧ (False → (p5 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h14
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122730504920290459317884291435 : ((((p1 → p2) → ((p5 ∧ (p2 ∨ (p4 ∨ (p1 ∨ False)))) ∧ (((p2 → p1) → ((p3 → p3) ∧ p1)) ∧ False))) → (p4 → p4)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196695975265329752059233934525 : ((((p1 ∧ ((p5 ∧ p2) ∧ True)) ∨ p1) ∧ False) ∨ (False → ((p5 ∨ p2) → ((False → p4) ∨ (((True ∧ p4) → (p1 ∧ p4)) → (p1 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_647957657889138154957909019321 : ((((((((((True ∧ (p4 ∨ p1)) ∧ ((p5 ∧ (True ∧ p1)) ∨ p1)) ∨ (p2 → False)) ∨ p4) ∧ p2) → (p5 ∧ True)) ∧ p2) ∧ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356781756912480058762776593888 : (p5 → ((p3 ∨ (p4 → (p2 ∧ (p4 → False)))) → (((True ∧ ((p1 ∨ (p1 → ((p4 ∧ (True → p3)) ∨ True))) → p3)) ∨ True) → (p2 ∨ p5)))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192869994074730686956453352708 : ((((True → p5) ∧ (p1 ∨ (False → p1))) ∧ (False ∨ p2)) → (False ∨ (((p1 ∨ (p5 ∧ (False ∧ (False → p3)))) ∧ (p3 ∨ False)) ∨ (p5 ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303983634402503613105592430729 : (p1 ∨ (((p2 ∨ p2) ∧ ((((p4 → True) ∧ p4) ∨ (False ∨ False)) → (((((p5 ∨ p3) → p5) → p5) ∧ (p3 → p5)) → (False ∧ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148685753256535692147815652474 : ((((False ∧ p1) ∨ ((False ∧ p5) ∨ (p5 ∨ True))) ∨ (p1 → ((p3 ∨ (p4 ∧ (True → (p5 ∨ p4)))) ∨ p2))) ∨ (p2 → ((True ∨ p5) ∧ False))) := by
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
theorem thm_5_vars_223336039997565826592634729398 : ((True ∨ (p2 ∧ p1)) ∧ ((((True ∨ ((((p3 ∧ (p3 ∧ p3)) ∧ p1) ∧ (p2 → p4)) → p1)) → (p2 → p2)) → (p2 ∧ (p5 ∨ p2))) ∨ True)) := by
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
theorem thm_5_vars_187517864697808283907233890533 : ((p1 ∨ (((p4 ∨ (p1 → False)) → p3) → (False ∨ (False ∧ p5)))) → (((p2 ∨ (p3 ∨ (p5 ∨ (True → (p3 → (p2 ∧ p4)))))) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_180246040836466217822154139061 : (((True ∨ ((((p4 ∨ True) ∨ False) → True) ∨ ((p4 → p3) → p5))) → p4) → ((p1 → (p3 ∨ False)) ∨ (False ∨ (p2 ∨ (False ∨ (p1 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791276497208036598018883962129 : (((True → ((((p3 → p5) ∧ (((False ∧ p4) ∨ (p2 → (p1 ∨ p3))) ∧ (((p3 ∨ p1) → p2) ∨ ((p5 ∨ p5) ∧ p3)))) ∧ p3) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326984063768931600810741947810 : (True → ((((p4 ∧ (((((True → (False ∨ (p4 ∨ True))) ∨ p5) → (p4 ∧ p3)) → (True ∧ p1)) → p4)) ∨ p1) → ((p1 → p4) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115810471447942462469205850678 : ((((p2 ∨ (p3 ∨ p3)) → p4) ∧ ((False ∨ ((p1 ∨ (True ∨ (p1 ∧ (p4 ∨ (p2 → (True ∨ p1)))))) ∧ False)) ∧ (p2 ∧ p3))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318615063276943398591852102639 : (p4 ∨ (((p2 ∨ (p5 ∨ p3)) ∨ ((((((p3 ∨ (p5 ∨ (p1 ∧ False))) ∨ (True → p5)) → True) ∧ (p2 → False)) ∧ p1) ∨ p5)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258767331985222947127198078055 : ((True → False) → ((True → ((p2 → (((p2 → (((p2 → p4) → True) ∨ (p3 → ((p5 → False) → True)))) ∧ p2) → (False ∨ p5))) ∧ False)) ∨ p3)) := by
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
theorem thm_5_vars_210185837302872824069452411303 : ((((p5 ∨ p3) ∨ True) ∨ True) ∧ (p4 → ((((False ∨ p3) ∨ (((p2 → p2) → (((False ∨ p4) → p2) ∧ (p3 ∧ p2))) → p3)) ∨ p3) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130301770526206241114908498610 : (((p3 ∧ ((p5 → (((False ∨ False) ∨ (p5 → (p5 ∨ (p1 ∧ p2)))) ∧ ((True → p3) → p3))) → False)) → (p3 → p5)) ∧ ((p2 ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → (((False ∨ False) ∨ (p5 → (p5 ∨ (p1 ∧ p2)))) ∧ ((True → p3) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h5
  -- False on the left can always be used.
  apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616083052787741923626847616060 : (((((p3 → ((True → ((((p3 ∨ (p5 ∧ False)) ∧ p1) ∨ False) ∨ p5)) ∨ p3)) → (((False ∨ (p3 → p1)) ∨ (p1 ∧ False)) ∧ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171438299075711778898637284527 : ((((p2 → p4) → ((p1 → ((False ∧ ((p3 → p4) ∧ True)) ∨ False)) ∧ False)) ∧ p2) ∨ (True ∨ ((p2 → (p4 → p5)) → ((p5 ∨ p5) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148922880350220072265982373801 : ((((p3 ∧ (p4 ∨ p1)) → p1) → (((True ∨ p4) ∧ p3) ∨ (((p1 → (p4 ∧ (p5 → p3))) ∨ p3) → p5))) ∨ (p3 ∨ ((p4 → p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69165291434088203979556315874 : ((p5 → ((p5 → ((p4 → ((False ∧ ((p5 ∨ ((p5 → p3) ∧ p1)) → p2)) → p3)) ∨ (False ∨ p4))) → ((p1 ∨ (p5 ∧ p3)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89280992870246178579645224741 : (((p5 ∧ (p5 → False)) ∧ ((((p5 ∧ ((p4 ∧ p4) ∨ (p4 → p2))) ∨ ((p3 ∧ (((p2 → p3) → p1) → p2)) → True)) ∧ p1) ∨ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h15 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h18 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h19 := h5 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h22 := h5 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180985487696871437656021984791 : (((False ∧ p5) ∨ (((p4 → ((p2 ∧ True) → p3)) ∧ False) ∨ (p1 → True))) → (((p1 ∨ p5) ∧ ((p5 ∨ p2) ∨ p3)) ∨ (p3 → (p3 ∧ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708500034960847375819246957241 : (((((((p3 → False) ∨ (True ∨ True)) ∨ True) ∨ p1) → ((p4 ∨ p2) ∧ (((p2 ∧ p5) ∧ p3) ∧ (((p3 ∨ p5) → (p3 ∧ True)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116251309012015923877003510380 : ((((p4 → p3) → p1) ∨ ((((p1 ∧ p4) → (p3 ∨ (p2 ∨ ((p1 ∧ p1) ∨ False)))) → (((p1 ∨ p2) → p1) ∧ False)) → p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193720367905044601169314744290 : ((p2 ∧ ((p2 ∨ (p2 ∧ (True → True))) → (p2 ∧ False))) → ((True ∨ (p4 → (p1 ∨ (p3 → ((False ∧ (p1 ∨ (False ∧ p3))) ∨ p1))))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p2 ∨ (p2 ∧ (True → True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∨ (p2 ∧ (True → True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336469235864152734069189100339 : (p1 → ((p2 → (((((False ∨ p2) → p2) ∧ (((p1 ∨ p2) → ((False → (p5 ∨ p5)) ∧ p4)) → (False ∨ (p1 ∧ p4)))) ∨ p5) → p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962424820410089553463910018034 : ((((True → False) ∧ (p2 ∨ (((True ∨ (((False ∨ True) ∧ p3) ∨ (p1 → p4))) → True) → ((p1 ∨ p1) → (False ∨ ((p2 ∨ p1) → p5)))))) → p4) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118510929015994550616984967494 : ((p3 ∨ ((p4 ∧ (p5 ∧ (p5 → p5))) ∨ (p5 → (((((p5 → ((p5 ∨ False) ∨ p5)) ∧ (p4 ∨ True)) → p4) ∨ True) → False)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113386463764415302040002737941 : (((True → (((p5 ∨ (p2 ∨ p2)) ∨ (p5 → (True ∨ (((p4 ∧ p1) → p2) ∧ True)))) ∧ ((False ∨ p3) ∧ p3))) ∧ (p1 ∨ p5)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310124810479865482257943399366 : (p2 ∨ (((((p4 ∨ p5) ∧ p5) ∨ False) ∧ ((((p3 ∧ p5) ∧ p3) ∨ True) ∨ p1)) ∨ ((p3 → ((p4 ∨ True) ∨ (p4 ∨ p3))) ∧ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705965798202510881008670908120 : (((((False ∨ (p1 ∧ p3)) → (p5 → (p3 → p4))) ∧ (True → ((True ∨ False) ∧ ((p4 → (((p2 ∨ p3) → (p5 → p1)) ∧ p5)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125851739297178803446257774838 : (((False ∧ False) → (((p4 ∨ (p5 → (((False ∧ (p2 ∨ ((p4 ∧ (p3 → True)) → True))) ∧ (True ∨ True)) → p5))) ∧ p1) ∧ p4)) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158447820539055447370339494769 : (((p4 ∨ p3) ∨ (((p5 ∨ p1) → ((p3 ∨ (p3 → (p2 → p5))) ∨ p3)) ∨ (True ∨ (p3 → p2)))) ∨ (p2 ∨ ((False ∧ p4) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_731921595152166811753510441082 : ((((p5 → (p1 ∨ False)) → (((True ∧ False) ∨ False) ∨ (((False ∨ (((p2 ∧ False) ∧ p1) → p2)) ∨ (p5 ∨ ((p4 ∧ p1) → p1))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142207780690353613611268062485 : ((p1 ∧ ((((p5 → p2) ∨ p4) ∧ (p1 ∨ p5)) ∧ ((p5 → (p4 ∧ ((True ∨ p5) → ((False → p3) ∧ p5)))) → False))) → ((p2 ∨ True) ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
    cases h7
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55944233685113172272643080703 : (((p3 → (p1 → (p1 ∧ p2))) ∧ (((((((p1 ∧ (False → (p4 ∨ (True → False)))) ∧ p1) ∨ p3) ∨ p5) → (p2 ∨ False)) ∨ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305528446287267710575273753503 : (p1 ∨ (((p4 → (p3 ∧ (p5 ∨ ((p3 ∨ p2) ∨ (p2 → p4))))) → (True ∨ p4)) → ((p5 → (((True ∧ p2) ∧ p1) ∧ p4)) ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684281039876610213446762647651 : ((((((p5 ∨ (((p3 ∧ (p1 ∧ p5)) ∨ (p3 ∧ p4)) ∧ p2)) → p5) ∨ (p1 ∨ (p5 ∧ p5))) ∨ ((p3 ∧ (p4 → False)) ∧ (p2 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174501381767121011807016393959 : ((((p2 → (p3 → (p5 ∨ p5))) → p4) ∨ (p5 → (((p5 ∧ True) ∧ p3) ∨ p1))) → ((((True ∨ False) ∧ (False → (p2 ∨ p2))) → p2) ∨ True)) := by
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
theorem thm_5_vars_249204823980637398881973908289 : ((p4 ∨ p3) ∨ ((p1 → p1) → ((((p1 → ((p3 ∧ p4) ∨ (False ∧ (False ∧ (p1 ∧ (p3 → p2)))))) ∨ True) ∨ (p2 ∨ False)) ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354810835643588502001136123044 : (p5 → ((((p3 → False) ∨ (p4 ∨ False)) → ((((p4 ∨ (False ∨ (p1 → (False ∧ p3)))) → ((True → p1) ∨ p4)) → p1) ∨ (p5 ∨ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585383071508453771154977991588 : (((((((p1 → ((True → p4) ∧ (p5 → p4))) ∨ ((p1 ∨ ((p5 → True) ∧ (p3 ∨ ((p3 ∨ p1) → p5)))) ∧ p3)) ∧ p2) ∧ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51499931508671282471183478472 : ((((p4 ∨ (p4 → False)) ∧ (((((p5 → (p4 → True)) → p1) → p3) ∨ (p4 ∧ p3)) → True)) → ((p3 ∧ (True ∨ (False → True))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684058294491554085918703243719 : (((((p2 ∨ ((p1 ∨ (((((p3 ∨ p5) → p4) ∧ p3) ∨ False) → p4)) ∧ (p3 ∨ p5))) → p3) ∨ (((True ∨ p5) ∧ p1) → (p4 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704900068798910163644525774532 : ((((p3 ∨ ((True ∨ p4) ∧ (True ∧ (True → (False ∧ False))))) → (((p4 → (True ∧ p3)) ∨ (False ∨ p3)) ∧ ((p1 → (p3 ∨ p4)) ∨ p2))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h27 := h25 h26
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h22.left
      let h31 := h22.right
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h33 := h31 h32
      -- We need to get the left conjuct of h33 based on <expert-advice>.
      let h34 := h33.left
      -- False on the left can always be used.
      apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171850300190174495770535428056 : ((((p4 ∨ p2) ∨ (p1 → (False → ((p5 ∧ p5) → ((True ∧ p4) ∧ p3))))) → False) ∨ ((False ∧ p1) → ((p3 → (p3 ∧ (p3 ∨ p2))) ∨ p2))) := by
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
theorem thm_5_vars_179429141349384845290722422660 : ((p4 ∨ ((p2 → False) → ((True ∧ ((p1 ∨ p5) ∧ (p2 ∨ False))) ∧ p2))) ∨ (p5 → ((((p1 ∧ (p5 → False)) ∨ p4) ∨ (p2 ∧ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755811374641620800145710924780 : (((p1 ∧ ((p2 → (((p1 ∧ ((False ∨ ((p5 → (False → p5)) ∧ (((False ∨ (p1 → p5)) ∨ p2) ∨ p5))) → True)) → False) ∧ False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



