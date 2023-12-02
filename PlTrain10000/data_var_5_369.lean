variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184751164622334848047778672728 : ((((p3 ∧ False) ∨ (True ∧ p5)) ∧ (p5 ∨ ((p4 → p2) → p1))) ∨ ((p5 ∨ (((p5 → (p5 ∨ (p4 ∨ (p2 ∧ p5)))) → p1) → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p5 ∨ (p4 ∨ (p2 ∧ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193427113379334619348134794102 : (((p4 ∨ p3) ∧ (p2 ∨ ((p4 → (False ∧ p2)) ∨ p4))) → ((((p1 ∨ True) ∨ (((p4 ∨ False) → (False → p4)) ∧ p3)) → (p5 ∨ p3)) ∨ p4)) := by
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
        exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16947912615272569580236142227 : (((p1 ∨ (p1 ∨ (((False ∧ (p5 ∨ p5)) ∨ (False → (((p3 ∨ (False ∨ (p2 ∧ True))) ∧ p5) ∧ True))) ∨ p2))) ∨ ((p1 ∨ p3) ∧ p4)) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134153822080651292807512051897 : ((((p3 ∧ ((p1 ∧ (p5 ∨ p5)) ∨ (p5 ∧ ((((p1 ∧ p1) ∧ True) ∧ True) → False)))) ∨ ((p4 → p5) ∧ p2)) ∨ p2) ∨ ((True ∨ p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234016630894995718787646434869 : ((p5 ∨ (p4 ∨ p3)) → (p4 → ((((p1 ∨ (p3 ∨ False)) ∧ ((p2 ∧ ((p5 → False) ∨ p5)) ∨ p5)) ∨ p3) ∨ ((p2 ∧ p2) → (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81505067328032239814450744465 : ((((((p3 ∨ (p2 ∨ (p2 ∨ (p2 ∨ False)))) ∨ p4) ∨ True) → (False ∧ ((p1 → p2) ∧ (True → (p3 ∧ p4))))) ∨ (False ∧ (True ∧ True))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p3 ∨ (p2 ∨ (p2 ∨ (p2 ∨ False)))) ∨ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184920875781638008286198997635 : (((p1 ∧ (p2 ∨ False)) ∨ ((p5 ∧ True) → ((p3 ∨ p3) ∨ p5))) ∨ (((p2 ∧ p5) → (p3 ∨ (True ∧ (True ∧ False)))) ∨ (True ∨ (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801023808213970305805537668398 : (((p2 → ((((p2 ∧ p4) ∧ ((p3 → ((p2 ∧ (p4 ∨ ((p3 ∨ True) ∨ False))) ∧ p1)) ∧ (p1 ∨ p3))) → False) ∨ (p5 ∧ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609520738676721928217096843257 : (((((p2 ∧ ((((p5 ∧ (((p4 ∨ False) ∧ False) → p1)) ∧ p5) ∧ ((p3 ∨ p5) → False)) ∨ ((False ∨ (p5 ∧ p1)) ∨ p2))) ∨ True) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_350308438396601799900115406167 : (p4 → ((p3 ∨ (p3 ∨ (True ∧ (((True → p1) ∧ True) ∨ ((False ∧ (p2 ∧ ((((p2 ∧ p5) ∨ (p3 → True)) ∨ p3) ∧ p2))) ∧ p4))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119280271917867808597415474904 : ((p3 → ((((p2 ∨ ((((((p1 → p2) ∧ True) → p1) ∧ (False → False)) → p3) → False)) ∧ ((p1 → p1) ∨ True)) ∧ p4) ∨ p3)) ∨ (p5 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586429476977781698697746749159 : ((((((p2 ∨ ((p1 ∨ p3) ∨ p2)) → (p3 ∧ (p5 ∨ (False → (True ∧ (p4 → ((p2 → True) ∨ ((p3 ∧ p2) ∨ p2)))))))) ∧ p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140324417045691566574045249102 : (((p4 → (p5 → (p5 ∨ (((False ∨ ((p1 ∨ (p5 → p4)) ∧ (False → p5))) → p3) → p5)))) ∧ (p4 ∨ (False ∧ p5))) → ((True → p3) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669343769528327570168428352444 : (((((((p2 ∨ p2) ∨ False) → (p3 ∧ ((p3 ∨ (False ∧ (p2 ∧ False))) ∧ ((p5 ∨ p1) ∨ False)))) ∧ (True → p1)) ∨ (p3 → (False → p4))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338116957941622016750316093594 : (p1 → ((p3 → (((p3 → p2) → p5) → (p1 ∨ p4))) ∧ (True → (True ∧ (p2 → ((((p3 → p4) ∧ (p2 → p4)) ∨ (p2 → True)) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737959938530611100329021807622 : ((((True ∧ p4) ∨ ((((((p1 ∨ True) → (p3 ∧ p4)) ∨ ((p3 ∨ False) ∧ True)) ∨ (False ∧ ((False → p3) → p5))) ∧ False) ∨ (True ∨ p1))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55207197970589708223138152495 : ((((False ∧ (p1 ∨ p1)) ∧ (p4 ∧ p2)) ∨ ((True → (p2 ∨ ((p1 → (p4 → p2)) → ((((p3 ∨ p3) ∧ p2) ∨ True) ∨ p2)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115090520734953050092329511280 : (((True → (((p1 ∧ p1) ∨ True) → ((False ∧ (True ∨ p5)) ∨ p4))) ∨ (p1 ∨ (True ∨ (((p1 → p1) ∧ (True ∧ p5)) ∧ p3)))) ∨ (p3 ∧ p5)) := by
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
theorem thm_5_vars_57027315836664640889239517336 : (((p1 → (False → False)) ∧ (p3 → ((True → ((p1 → p4) ∨ (p1 ∨ ((p5 ∨ p4) ∧ (p2 ∨ ((p5 → (p2 → False)) → p3)))))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350955221129799429872275587279 : (p4 → ((((p4 → True) ∧ ((True ∧ p3) → ((False ∧ False) ∨ (True → (p3 ∧ p2))))) ∧ (((p5 ∨ p3) ∧ (p3 ∧ p5)) ∨ p5)) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156940139806148496000467246362 : (((((((False ∧ p5) → p4) → p5) ∨ (True → ((False ∨ p2) ∧ (True → True)))) ∨ (p4 ∧ p2)) ∨ True) ∨ ((False → False) → ((p1 ∧ p4) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53920102088644797548448713078 : (((p2 ∨ ((p1 → (True ∧ (False ∧ p3))) ∨ (p1 ∧ p3))) ∨ (((True ∨ ((((p5 → p2) ∧ True) ∧ True) → p5)) → (p2 ∧ p4)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645197020309345716805269560345 : ((((p3 ∨ ((p5 → (p3 → False)) → (p2 → (p5 ∨ (p1 ∨ (((p3 ∧ p3) ∨ (p4 ∨ (p3 ∨ p5))) → (False ∧ (p4 ∧ p5)))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346294702998723912221286414758 : (p3 → (((((p5 → (p2 ∨ (p4 ∨ (p2 ∨ ((((p2 → p2) → p2) → False) ∨ (p3 → p3)))))) → p3) → (p2 ∨ p5)) ∨ True) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191601916324884299901722572719 : ((p3 ∧ (((p3 ∧ p1) → ((p4 → p1) → p2)) ∨ p2)) ∨ ((p5 → (((p4 ∨ False) ∨ (((p5 ∧ (p4 ∧ True)) ∨ False) ∧ p4)) ∨ p5)) ∨ p5)) := by
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
theorem thm_5_vars_59986654383199164151586027042 : (((False ∨ p2) → ((p2 ∨ (((((((p3 ∧ False) ∧ p3) ∨ p1) ∨ p2) → p3) ∨ True) ∨ ((True ∨ ((p3 ∧ p2) ∨ p4)) → True))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62289296413940308714159168206 : ((p3 ∧ ((p2 ∧ ((True → (((p5 → ((p3 ∧ p3) ∧ p4)) ∧ (p1 ∨ p1)) ∧ True)) ∧ ((False ∧ True) → (p3 → (True ∨ p4))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136679155101382807923893112908 : (((False → (p1 → p4)) → ((((p2 → (p3 ∨ p5)) → p1) ∧ ((((p5 → p2) → (p3 ∨ p2)) ∧ True) ∨ p2)) ∨ p4)) ∨ ((True ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171525974171102145104818317463 : (((((((p3 ∨ ((False ∨ (p4 → p1)) → p3)) ∨ True) → False) ∨ p2) ∨ p1) ∨ p5) ∨ (True ∨ (False ∧ ((False ∧ (p2 ∧ p3)) ∨ (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157693289880566286217157193544 : ((((((False → (True ∨ (((p4 → p2) ∧ p1) ∨ p5))) → p3) ∨ p5) ∧ p1) → (p5 ∧ (p3 → False))) ∨ ((True ∨ (p2 → p2)) ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185012736869966028136059092966 : (((False ∨ p3) ∧ (p4 ∨ (p2 → (p3 ∨ ((p4 ∧ p1) ∨ p3))))) ∨ (((True → p2) → (p4 → p4)) ∨ ((p2 ∨ p1) → ((p1 → p4) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196711790625155780189925402609 : ((((((p4 ∨ p4) ∧ False) ∨ p5) → p4) ∧ p1) ∨ ((False → False) ∧ ((p3 → ((((p5 ∨ False) ∨ p3) → p1) → (p1 ∨ False))) ∧ (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ False) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46238484191095490525886986347 : ((((((p4 ∨ p1) ∨ (p3 ∨ p3)) ∧ (p2 ∧ (((p1 ∧ p2) ∧ p3) → (False → ((p4 ∧ p1) → p3))))) ∨ (False → p4)) ∧ (False → False)) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256604834536311299460700110068 : ((p1 ∨ True) → ((True → (((p1 ∨ p3) → False) ∧ False)) → (p2 ∧ ((True ∨ ((((p2 ∧ p2) ∧ p3) ∧ (p4 ∧ (p4 ∧ p3))) → p1)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h24 := h2 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321080583594016239730640045431 : (p4 ∨ (p1 ∨ ((p5 ∨ (p4 → p1)) ∨ (((((((p4 ∧ p5) ∧ (p4 ∨ False)) ∨ (p5 → p2)) ∧ True) → p2) → p2) → (p4 ∨ (True ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_681833587958999691937606607982 : ((((((p4 ∧ p1) ∧ (p4 ∧ ((True ∨ (p5 ∧ (True ∧ ((p2 ∨ p4) ∨ p1)))) ∨ p4))) ∧ False) ∧ (p5 ∨ (((p3 ∧ p5) → p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178909910329526740368271007296 : (((p5 ∨ p3) ∧ (((p5 → (p1 ∧ False)) ∨ p1) ∨ ((False ∨ p3) → False))) ∨ (p2 ∨ (p5 → (True ∨ (((False ∧ p3) ∨ p4) ∧ (p3 → p2)))))) := by
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
theorem thm_5_vars_187538319616972635468604692571 : ((p2 ∨ (((False ∨ p5) ∧ ((p2 → p2) → (p2 ∨ p2))) ∨ p2)) → (p2 → (p4 ∨ (((((p2 ∨ p4) ∧ (p3 ∨ True)) ∨ p2) ∧ True) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230725663319894257267861813841 : (((p5 → False) ∧ p2) → ((p2 → (p5 ∧ (((p5 ∨ p3) → (p3 → (True → False))) ∧ (p3 ∧ ((p1 ∨ (p5 → (False → p2))) ∧ p3))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754837242182966195857012784039 : (((False ∧ (p1 ∨ (p4 ∨ (((p4 ∨ p5) ∧ (((p2 ∨ p4) ∨ p3) ∨ ((False ∨ ((p2 ∨ ((p3 ∧ p2) ∨ True)) ∨ p2)) ∧ p2))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124732739844250560075211296525 : (((((p1 ∧ False) → True) → p1) ∧ (((True ∨ p5) ∨ p4) ∧ (p3 → ((p2 → (p2 → True)) ∨ (((p2 ∧ p4) ∨ p1) ∧ False))))) → (p3 → p1)) := by
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
      have h9 : ((p1 ∧ False) → True) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 ∧ False) → True) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h13
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : ((p1 ∧ False) → True) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h17
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173668624271118359121773382203 : (((((((p4 → p1) ∨ ((p2 ∧ p1) ∨ p3)) → (p2 ∨ p3)) ∨ p1) ∨ p4) ∨ p1) → (p1 → (((p1 ∨ p1) ∨ p2) → ((False ∧ p3) ∨ p1)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
            exact h2
          case inr h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608320315323382942474823216238 : (((((((True → (True ∨ (True → (p1 ∧ p4)))) ∧ ((p4 → ((p3 → False) ∧ (p2 ∧ p1))) ∧ ((p5 ∧ p3) ∧ p5))) ∨ p3) ∨ True) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_9659008223138597475029574438 : ((((False ∧ True) ∨ (((p1 → True) ∧ (True ∧ (p3 → ((True ∨ (True → p3)) ∧ ((((p3 ∧ p5) ∨ p5) → p1) → p2))))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119557722901739812943396254409 : ((p5 → (((((p1 → (True → (p2 ∨ (p1 ∨ False)))) ∧ (p1 → False)) → False) ∧ p1) ∨ (((p2 ∧ p1) ∨ (p4 ∨ p3)) ∨ p5))) ∨ (p4 ∨ p3)) := by
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
theorem thm_5_vars_114773975116035000903173595843 : (((((p1 ∧ p3) ∧ (p5 → ((p4 ∧ p5) ∧ ((p5 ∧ p3) → p4)))) ∧ True) ∧ (((p1 ∨ ((p3 ∧ p3) → p5)) ∧ p3) ∧ p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152309858625208089297191911091 : ((((p4 ∧ (p3 ∨ p5)) ∨ p2) ∧ (False ∨ (p3 ∨ (p3 ∨ (p4 ∧ (p2 ∧ (p4 → (p3 ∧ (p3 ∧ False))))))))) → (((True → p5) ∧ p1) → p5)) := by
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
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h15 := h3 h14
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h18 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h19 := h3 h18
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
            have h25 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h21
            -- We have shown the premise of h24, we can now drive its conclusion.
            let h26 := h24 h25
            -- We need to get the right conjuct of h26 based on <expert-advice>.
            let h27 := h26.right
            -- We need to get the right conjuct of h27 based on <expert-advice>.
            let h28 := h27.right
            -- False on the left can always be used.
            apply False.elim h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h29
          case inr h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- One of the premise coincides with the conclusion.
            exact h29
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h41 =>
      -- False on the left can always be used.
      apply False.elim h41
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h44 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h45 := h3 h44
        -- One of the premise coincides with the conclusion.
        exact h45
      case inr h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h46
        case inl h47 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h48 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h49 := h3 h48
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h50 =>
          -- Conjunctions on the left can always be decomposed.
          let h51 := h50.left
          let h52 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h53 := h52.left
          let h54 := h52.right
          -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
          have h55 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h51
          -- We have shown the premise of h54, we can now drive its conclusion.
          let h56 := h54 h55
          -- We need to get the right conjuct of h56 based on <expert-advice>.
          let h57 := h56.right
          -- We need to get the right conjuct of h57 based on <expert-advice>.
          let h58 := h57.right
          -- False on the left can always be used.
          apply False.elim h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137988499356283348659939446016 : ((p5 ∨ (True ∧ ((p2 ∧ (False ∧ p4)) ∧ (((p5 ∨ ((p1 ∧ p4) ∧ True)) ∧ ((p3 → (p4 ∧ p4)) ∨ p2)) ∨ p1)))) ∨ ((p4 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116564166388466991350584468684 : (((p2 ∨ p2) ∧ ((False ∧ ((p5 ∧ p3) → (p2 → (p1 ∧ ((True ∧ ((p1 ∧ (False ∧ True)) ∨ True)) → (p1 ∨ False)))))) ∨ p4)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219331603107132780385500039983 : ((p2 ∨ (p1 ∨ (p1 ∨ p2))) → ((p3 ∨ ((p1 ∧ ((p2 ∨ p5) ∧ (((p3 → False) → (p3 → (p5 → True))) ∧ True))) ∧ p4)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147987125304062637691355836884 : ((((((True ∧ ((False ∧ p3) → ((p2 → p5) → (True → False)))) ∧ p4) ∧ (False ∧ p3)) ∨ False) ∨ (False ∨ p2)) ∨ (True ∧ (p2 → (True ∨ p3)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62477816551252855908335474035 : ((p3 ∧ ((p1 ∧ p3) → ((p2 ∧ (p5 ∧ p5)) ∨ ((((False ∧ (True ∧ False)) ∨ (p1 ∧ True)) ∨ (p4 ∨ (p1 ∨ p2))) ∧ (False ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56292899045455570019106565953 : (((((p2 ∧ p1) ∨ p3) ∧ p2) → ((True ∧ (p2 ∨ (p1 ∨ False))) → (((p4 ∧ p4) ∧ p5) ∨ (((p4 ∧ (p3 ∧ p1)) ∧ p1) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387319056717945874542200804190 : ((((((p1 ∧ (((((p3 ∨ (p5 ∨ (False ∨ True))) ∧ (p5 → True)) → False) → p1) ∨ (False → p3))) ∧ p5) ∨ ((p4 ∧ p3) → p3)) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156792179616333945198440987555 : (((p3 ∧ (((p4 ∨ ((True ∨ ((p5 → p2) → ((p1 ∧ p5) ∨ True))) ∧ p4)) ∧ p3) ∨ p1)) ∧ p4) ∨ (p1 ∨ ((p5 ∨ True) ∧ (p3 → p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690735672063211545465419470718 : (((((((False ∧ False) ∨ ((True → p2) → ((False → (p1 ∨ p1)) ∨ False))) ∨ p1) → False) → (((p1 ∧ ((True ∨ p3) ∧ p4)) ∧ p4) ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ False) ∨ ((True → p2) → ((False → (p1 ∨ p1)) ∨ False))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598562232483853491844496801757 : (((((True ∧ (p2 → False)) → (((p2 ∨ (p5 ∨ (p5 ∧ True))) → p1) ∨ ((p4 ∨ (p2 ∧ ((True ∧ p5) → (p2 ∨ p1)))) → p2))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_827754448104874087853832469 : ((p5 ∧ (((p3 ∨ p1) ∧ (p4 ∨ (p1 → ((p3 ∧ ((p5 ∨ p2) → True)) ∧ (p5 → (p2 ∨ ((True ∨ p5) ∨ p1))))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261729041653519966337274205337 : (True ∧ ((((((p3 ∧ (((p5 → p2) ∧ p5) ∧ p4)) ∨ p4) ∧ (True ∧ (p1 ∨ p4))) → ((p2 ∨ (p2 ∧ (False ∨ False))) ∨ p3)) ∨ True) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301990989065308246187614706853 : (False ∨ ((p3 → p4) → ((((p3 ∧ ((p3 ∨ p5) ∧ p2)) ∧ ((False ∧ p4) ∨ p2)) ∨ (True → (((p4 ∨ p1) ∧ (p3 ∨ p1)) ∨ True))) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725728683954722459018777576324 : (((((p1 ∨ p2) ∧ p2) ∨ ((p2 ∧ False) ∧ (((((p5 ∨ (((True ∧ (False → p3)) ∨ p5) → p4)) ∧ p4) → True) → p3) → (p3 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111693781942017920698874979599 : (((((((((p3 ∨ (p2 → (False ∧ p2))) ∧ ((p5 ∨ p2) → p2)) ∧ (p2 ∧ p1)) ∨ p3) → (p3 ∧ p4)) → True) → p3) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64930420634353568127572761741 : ((p2 ∨ (((True ∨ p4) → (((((p5 ∨ True) ∧ (True → p5)) ∧ p3) ∨ True) ∧ True)) ∨ (((True ∧ (p5 ∨ p2)) → p5) ∧ (p2 → p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209120681916116041485739933853 : ((p2 ∨ (p3 ∨ (p4 → (p2 → True)))) → ((((p2 ∨ False) ∨ p4) ∨ (True ∧ (((True ∧ (p2 ∨ p1)) ∨ False) → p4))) ∨ ((p3 ∧ p2) → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928110851571157608402063387575 : (((((True → False) ∧ (False → (p1 ∨ (p2 ∨ (p3 ∧ True))))) ∧ (p1 → (p3 → (True ∧ (p2 ∨ ((False ∨ (p4 ∧ (p1 → True))) → p2)))))) → p2) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621458272536744436453805619026 : ((((False ∧ ((True → (((False ∨ (p4 ∧ False)) ∧ (True ∧ (((False ∨ (p3 ∨ False)) ∧ p3) → True))) ∨ ((p4 ∨ p3) ∧ p1))) ∧ p3)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159153998464078295108572186351 : ((p1 → (((True ∧ p2) ∧ (((p2 ∨ (((p2 → p2) → p1) → (p3 ∧ p5))) → False) ∨ False)) ∧ p1)) ∨ ((p4 ∧ (False ∨ p2)) → (p1 → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49169536641510171465016714402 : (((((p3 ∨ (p2 ∧ (p5 ∨ True))) ∨ p3) → ((p5 ∧ p3) ∧ ((False → (p2 ∨ p4)) ∨ ((False → p5) ∧ True)))) ∨ (p3 ∧ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148747168965139154217486460380 : ((((p1 → True) ∧ ((False ∧ True) → p4)) ∧ (p3 → ((((p4 ∨ p4) ∧ (p5 → p5)) → (p5 ∨ p1)) ∨ True))) ∨ ((True ∧ p2) ∧ (False ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96290690363557788522112024887 : ((False ∨ ((((p2 ∨ (False ∨ (p1 ∨ (p2 → (p1 ∨ (p1 ∨ p2)))))) ∨ (p3 ∨ (False ∨ ((p4 ∧ p3) ∧ (p5 → p3))))) → False) ∨ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : ((p2 ∨ (False ∨ (p1 ∨ (p2 → (p1 ∨ (p1 ∨ p2)))))) ∨ (p3 ∨ (False ∨ ((p4 ∧ p3) ∧ (p5 → p3))))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h5
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49588180213622097873029974742 : ((((False ∨ (p5 ∨ (((p3 ∨ p3) ∨ ((p2 → p1) ∨ p1)) ∨ False))) ∧ (True ∨ ((p5 ∧ p4) ∧ (p4 ∨ True)))) → (p5 → (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49480548015089532337590274786 : (((((p2 ∧ ((p1 ∧ ((p2 ∧ True) → (p5 → (False → (False → (False ∨ p4)))))) → p4)) ∨ (p2 ∧ p2)) → p5) → ((p3 → p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310288872974484165527059681940 : (p2 ∨ (((((True ∧ False) ∧ (p2 → p4)) → (p4 ∧ p5)) ∧ p5) ∨ (((((p2 ∧ (p1 → ((True → p4) ∧ p2))) → p1) ∧ p2) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183918867830431917777605385822 : (((p1 ∧ ((p5 → (p3 ∧ (False ∨ True))) → (p2 ∨ p3))) ∧ False) ∨ (p5 → ((False → p1) → ((p3 ∧ (((p3 → p1) → p4) ∧ p3)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675042626254262373084733371714 : (((((p2 ∨ (p1 ∨ ((p2 → (((p5 ∨ True) ∨ True) ∧ ((p4 → (p3 ∨ p2)) → p5))) ∨ p4))) ∧ p1) ∧ ((p5 → (False → p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357519293072856943827300720315 : (p5 → (True ∧ ((True → (True ∨ True)) → (((p1 → (True ∨ p2)) ∨ p4) → (((p2 ∨ ((p3 ∨ p3) ∧ p3)) ∧ (p2 → p3)) ∨ (False ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131932708289020124818063747655 : (((p3 ∨ p4) ∨ (((p3 ∨ ((((p5 ∨ p2) ∧ False) → (p3 ∨ (p2 ∧ p3))) → ((p3 → False) ∨ p1))) ∧ False) ∨ True)) ∧ (p2 → (p1 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50364847938258028597496954009 : (((((p3 ∧ p2) ∧ p1) ∨ ((((p3 ∧ True) ∧ True) ∧ (p2 ∨ False)) ∧ ((False → (p4 → False)) ∨ p5))) ∨ (True ∧ (True → (p4 ∨ True)))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196831209838570181220669958201 : (((p3 ∧ (((p5 → p1) → p3) ∧ p3)) ∧ p1) ∨ ((False ∧ ((p3 → (True ∧ False)) ∨ (p5 ∧ (True ∧ ((True ∨ (p3 ∧ False)) ∨ p3))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148947966581015010370302665100 : (((p4 → (False → (False → True))) → (((p5 ∨ (True ∧ (p3 → p2))) ∨ True) ∨ (((p1 ∧ p5) → p4) → p1))) ∨ (p5 ∨ ((p5 ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164842480312216584965110714348 : (((p3 ∧ (((p5 ∧ (p1 ∧ True)) ∧ p3) ∧ (False ∨ (((p5 → p3) ∧ False) ∧ p2)))) ∨ p2) ∨ ((((p3 ∧ p5) ∨ p4) ∧ (p5 ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160315639193793906240109244181 : (((((p5 ∨ (False ∨ p3)) ∧ p5) ∨ ((((False ∨ (p4 ∧ True)) ∧ p3) → p4) ∨ p5)) → (p5 ∧ False)) → (p5 ∨ (p5 ∨ (p4 ∧ (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (False ∨ p3)) ∧ p5) ∨ ((((False ∨ (p4 ∧ True)) ∧ p3) → p4) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305287516816624686193667343750 : (p1 ∨ (((False ∨ (((p3 → (True → (False ∨ ((p2 ∨ (p5 ∧ p2)) → True)))) ∧ p2) → p4)) ∧ p4) ∨ (((p3 ∨ (p2 ∨ p2)) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48404641119321517563248528428 : (((p1 → ((False ∧ (p3 → p5)) ∨ (True → (p1 ∨ (p4 ∧ (True → (((p2 ∧ False) ∨ True) → ((False ∧ p1) → p5)))))))) → (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158614324787497507090116364760 : ((False ∧ ((p1 ∨ (p2 → p1)) → (((p5 ∨ p2) ∧ True) ∨ ((True ∧ (p1 ∨ (True ∨ p3))) → p2)))) ∨ ((((True ∧ p5) → p2) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84730688493711616786731150919 : (((((p4 ∨ False) ∨ (((p1 ∧ False) ∧ (p1 ∧ p5)) ∨ True)) → (p5 ∧ True)) ∧ ((p1 ∨ False) ∧ (p3 ∨ ((p2 ∨ p4) ∨ (True ∧ p5))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : ((p4 ∨ False) ∨ (((p1 ∧ False) ∧ (p1 ∧ p5)) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : ((p4 ∨ False) ∨ (((p1 ∧ False) ∧ (p1 ∧ p5)) ∨ True)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : ((p4 ∨ False) ∨ (((p1 ∧ False) ∧ (p1 ∧ p5)) ∨ True)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h18
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h23
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654558448404025022577077444730 : (((((p1 ∨ ((((True ∨ True) ∧ (p3 ∨ (p1 ∨ p1))) ∧ False) ∨ (((False → p4) ∧ (p3 → p3)) ∧ (p4 ∧ p2)))) ∨ p3) ∨ (p3 → p3)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_208443543396068740938930695702 : (((True → p2) ∨ (p2 ∧ (False ∧ p3))) → (((p5 ∨ p2) ∧ ((((p1 ∨ False) ∧ ((p5 ∨ p4) → (p4 ∧ p1))) ∧ p5) ∨ p5)) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754636837361762441618011039483 : (((False ∧ (p3 ∧ (p4 ∧ (((((((p2 ∨ False) ∧ p2) → (p3 ∨ True)) → ((p1 → p3) ∧ p4)) ∨ ((True ∧ p3) ∨ p4)) → p1) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299220566501218368313814793028 : (False ∨ (((p1 → (((((False ∨ p5) → p5) ∧ (p1 ∧ ((p1 ∨ p3) ∨ p2))) ∧ p3) → (p2 ∨ ((p5 ∨ p3) ∨ p4)))) ∨ (p2 ∨ False)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61973155438529600412263737068 : ((p2 ∧ ((p4 ∧ (((p5 → p1) ∧ (p5 ∧ p1)) ∧ (p3 ∨ p2))) ∨ (((p4 ∧ p4) ∨ p5) ∨ (p3 ∧ (p1 → ((p5 ∧ False) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352283294804270462020603743487 : (p4 → (((p2 ∧ p1) → (True ∧ p2)) → ((p1 ∧ p1) ∨ (p1 ∨ (False ∨ (False ∨ ((p2 ∧ p1) → (((False ∨ p5) ∨ (p4 ∨ p1)) ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44898954014404333886929960255 : ((((p4 ∧ (False ∨ p3)) → (((((p2 → ((p1 → p2) → p5)) ∧ (False → p1)) ∧ True) → (False → p2)) ∨ ((p4 → p5) ∧ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345297286078390784895615472677 : (p3 → ((p3 → (((p3 → ((p1 ∨ ((p1 ∧ p5) ∨ p1)) → (False ∨ (p4 ∨ p4)))) ∨ p3) → (((p2 ∧ (p5 ∨ True)) ∨ p2) ∨ p3))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9272021647783509020987637847 : ((((p2 ∧ (p1 → (p4 ∨ (p5 ∨ (p5 → p1))))) → ((((p1 ∨ p4) ∧ (False ∧ ((True → p5) ∧ p2))) ∧ True) ∨ (p4 ∨ True))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342504230005165148463959800120 : (p2 → (((((p3 ∧ (p2 ∨ p4)) ∧ (((p1 ∨ True) ∨ False) ∨ p4)) ∧ p2) ∨ p5) → ((((True → (False ∧ p1)) ∧ True) ∨ p2) ∨ (p4 → p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h24 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117206021399539782436567970948 : ((True ∧ ((((True ∨ (p3 ∨ True)) → p5) ∨ (p4 → p3)) → ((((p4 → (p2 ∧ p1)) → (p1 → p5)) ∨ (p1 → p2)) ∧ True))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119336103368827553055994888527 : ((p3 → ((True ∧ ((False → True) ∧ p3)) ∧ (((p3 → (True → ((True ∧ (True ∨ (p5 ∧ p3))) ∧ (p4 ∧ False)))) → False) ∧ p3))) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720295086268391052750265273444 : ((((((True → p2) ∧ p2) ∨ p2) → ((((p3 → p3) ∨ p2) ∧ (((p2 ∨ False) ∧ (((p3 ∨ p3) → p1) ∧ p1)) → (True ∨ p3))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41247213215000103347117764319 : (((((p1 ∨ (((p5 ∧ (p3 → (p2 ∨ False))) ∧ p4) ∨ (((False ∨ True) → p2) → p5))) ∨ True) ∨ ((p3 ∧ p1) ∨ (p3 → p5))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



