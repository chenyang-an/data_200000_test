variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171650947007955790908522264811 : (((True ∧ (((p2 ∨ True) → False) ∧ ((p4 ∧ (p1 ∧ (p1 → True))) ∧ p5))) ∨ p2) ∨ (p5 → ((p3 → p5) ∨ ((p3 ∧ (p2 ∨ p3)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173534218817950323055457863269 : (((((False ∨ (False ∨ p2)) ∨ (p3 ∧ False)) ∨ (False ∨ (p5 → (p2 ∧ p2)))) ∧ p2) → ((((p5 ∨ (p1 → p2)) → (p3 → p2)) → False) → False)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h11 : ((p5 ∨ (p1 → p2)) → (p3 → p2)) := by
            -- Implications on the right can always be decomposed.
            intro h12
            -- Implications on the right can always be decomposed.
            intro h13
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h14 =>
              -- One of the premise coincides with the conclusion.
              exact h4
            case inr h15 =>
              -- One of the premise coincides with the conclusion.
              exact h4
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h16 := h2 h11
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : ((p5 ∨ (p1 → p2)) → (p3 → p2)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h23
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149415284586675886098417696333 : ((True ∧ (((p4 ∨ (p2 → p5)) → ((p4 ∨ p2) ∧ p4)) → (((p1 ∧ (p3 ∧ p3)) ∨ p3) ∨ (p4 ∧ p1)))) ∨ ((p3 ∨ (p1 ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89211721642489096912316236035 : (((True ∧ (True → False)) ∧ ((p1 ∨ (((False → (p1 → ((False ∧ (p4 ∧ p5)) → (p5 → p3)))) ∨ p3) ∨ (p5 ∨ (p5 ∨ p4)))) ∨ p3)) → False) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h14 := h5 h13
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h17 := h5 h16
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h20 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h21 := h5 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h24 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h25 := h5 h24
            -- False on the left can always be used.
            apply False.elim h25
          case inr h26 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h27 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h28 := h5 h27
            -- False on the left can always be used.
            apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h31 := h5 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166112407174600428016142873703 : (((p5 → p3) → ((((p4 → p4) → (p5 ∧ p2)) ∨ (True → ((p1 ∧ p1) ∨ p4))) → p5)) ∨ (True ∨ (p5 → ((p5 → p4) → (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162863473775524736969597196206 : ((((((p3 ∨ (p5 ∧ p5)) ∧ (p4 ∧ p2)) → p1) → ((p1 → p2) → p4)) ∨ (p4 → p4)) ∧ ((p4 → True) → ((False ∨ (False → p3)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66479400264165436882833859433 : ((True → (((((((p3 ∧ p2) → False) → True) → (((p4 → (p5 → p1)) → ((False ∧ p5) ∧ p1)) → p2)) ∨ (False ∨ p5)) → p1) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73018704243175022401764583314 : (((((((p1 ∧ (((p5 ∧ ((False ∧ (p2 ∨ p3)) ∧ p5)) ∧ p3) ∧ (p3 → False))) ∧ (False ∨ p5)) ∧ p2) ∨ (True ∨ p2)) → False) ∨ p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((((p1 ∧ (((p5 ∧ ((False ∧ (p2 ∨ p3)) ∧ p5)) ∧ p3) ∧ (p3 → False))) ∧ (False ∨ p5)) ∧ p2) ∨ (True ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343573216995780163300721578735 : (p2 → ((True → False) → (p2 ∧ (p3 ∨ (p1 ∨ (((((p4 → ((((p2 ∧ p3) ∧ p4) ∧ p5) ∧ p4)) ∧ True) ∧ (False → p1)) → p5) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54088709998020733008933951803 : ((((p3 → p2) ∨ (p1 ∨ ((p2 → (False ∨ False)) ∨ True))) → (p3 ∧ ((p3 → ((p5 ∧ False) → p3)) ∨ ((True → p4) ∨ (True ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219497691487953702180803921685 : ((p5 ∨ ((False ∨ p4) ∨ p4)) → (((True ∧ ((p4 → (p5 → (p3 ∧ (((p4 → (True → (False → p3))) → False) ∨ p4)))) ∧ p5)) ∧ False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338692130200362090144640443814 : (p1 → ((p2 ∨ p1) ∧ ((((p2 → p5) → p2) ∧ (False ∧ False)) ∨ ((p3 → (p4 ∧ (False → p1))) ∨ (p1 ∧ (p2 ∨ (False → (p1 ∧ p3)))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51412934166632383797928453597 : (((((True ∧ p5) ∨ ((p5 ∨ ((p5 ∨ p2) ∨ ((p2 ∧ False) ∧ p5))) ∧ (p2 ∨ False))) → True) → (p2 → (((p1 → p4) → p4) ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737983292939943798459517591779 : ((((True ∧ p4) ∨ (p5 ∨ (((p3 → p2) ∨ (p1 → p2)) ∧ (p3 ∧ (((p1 → p2) ∧ ((p2 → p1) ∨ (p5 ∨ (False → p3)))) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225884585163911415254194084956 : (((p1 ∧ False) ∨ p2) ∨ ((p1 → p3) → (((False ∧ ((p3 ∨ p1) ∨ ((p5 → p4) ∨ p5))) ∨ p3) ∨ (((False → True) ∧ p2) ∨ (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65459451805401077390590662504 : ((p3 ∨ ((p5 ∨ p5) → (((p3 ∧ (((p1 ∧ p1) ∨ p1) ∨ p3)) ∨ (p5 ∨ ((False ∧ (p4 → (p4 → True))) → (p3 ∨ p4)))) ∧ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659816758416103962183852236069 : (((((p3 ∨ ((p3 ∧ (p3 → (((p5 ∨ (False ∧ p4)) → ((False → (True ∨ (p3 ∨ p1))) ∨ p3)) ∧ p5))) ∨ False)) ∧ p1) → (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735493885861846056096539665550 : ((((p4 ∨ p4) ∧ ((p4 ∨ p2) ∧ (p2 ∨ ((True ∨ (((p3 ∧ False) → p5) ∧ p3)) → (p1 → (((p3 ∧ (p3 → p4)) ∧ p3) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185944215224918821124574777067 : ((((True ∧ p3) ∨ (False ∨ ((p4 ∨ p3) → (p2 → p4)))) ∧ p4) → ((p4 → (p5 ∧ ((((p4 ∧ p2) ∧ p4) → p3) ∧ p5))) ∨ (p1 → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255874426216829716604836134272 : ((True ∨ p1) → (((p1 ∧ p3) → ((p3 ∨ p3) ∧ (p4 ∧ p4))) → ((p2 → ((((p3 ∧ p1) ∨ (p5 ∧ False)) ∧ p2) ∨ (False → p2))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146947882506259955737908192310 : (((((p2 ∨ (p3 → (p3 ∨ (False → False)))) ∧ (p3 → (((p5 → (p4 ∨ p1)) ∨ p4) ∨ p2))) ∨ True) ∧ True) ∨ ((p3 → (p3 ∨ False)) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300532177092260355126880897237 : (False ∨ ((((((p2 ∧ p1) ∧ p4) ∨ ((True → p5) ∧ (p5 ∧ ((p3 ∧ p5) → False)))) ∨ (p2 ∧ p5)) ∧ p2) ∨ (True → (p5 ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710179287070178941695345744652 : ((((((p1 ∨ (p4 → False)) → False) ∨ True) ∧ (p3 ∧ ((p2 ∨ (True ∨ ((p5 → (((p2 → (p4 ∨ p1)) ∧ p4) ∧ p4)) ∧ p5))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734887954497204742365179976774 : ((((p2 ∨ p3) ∧ ((True ∨ ((False ∨ (((p3 ∨ ((((p1 ∨ p4) → p1) ∧ (p2 ∨ p4)) ∨ True)) ∧ (p4 ∨ p5)) → p5)) → p5)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252039765991460957232469894315 : ((p4 → p1) ∨ ((p4 ∨ ((((False ∨ ((((True ∨ p3) ∧ True) ∨ p4) → p2)) → (p3 ∧ p3)) ∨ p5) ∧ (p4 ∧ p2))) → ((p3 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300960677074018785536414348717 : (False ∨ ((((False ∨ p5) ∧ (p3 → (p4 ∧ (p4 ∨ (True ∨ p2))))) → False) ∨ (((p5 → (p4 ∨ (p2 ∨ True))) → (p5 ∧ p1)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_311231761162395452086449610862 : (p2 ∨ ((p2 → p4) → ((((p5 ∧ p1) ∧ ((p3 ∨ p2) ∧ p1)) ∨ True) ∧ ((((((True → p5) → (p4 ∨ p5)) ∧ p3) ∨ p2) → p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_338129834853639654919632821033 : (p1 → ((((p2 → True) → (p2 ∧ p5)) ∧ (p3 ∨ p1)) ∨ ((((p1 ∧ p3) ∨ (((False ∧ p1) ∧ True) → ((False ∧ True) ∨ p1))) ∧ False) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152584652220865417223507452150 : (((True ∧ p1) ∧ (p3 ∨ (p1 ∧ ((p4 ∧ ((p1 ∧ p2) ∨ ((False ∨ p3) → (p1 ∧ (False → p1))))) ∧ p4)))) → ((False ∨ p3) ∨ (False → p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64143016921151981683083593471 : ((False ∨ (((p5 ∨ p2) ∧ p1) ∨ (((p1 ∨ p2) ∨ (((False → p1) → (False ∨ (p3 → p5))) ∧ (True ∧ p5))) ∨ ((True ∨ True) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353531825812609630708754663323 : (p4 → (p3 ∨ (((p2 ∧ ((False ∧ ((True ∨ ((p4 ∨ p5) ∧ True)) ∧ False)) ∨ (((p4 ∨ p3) ∧ p4) → ((p2 ∨ p5) ∧ p1)))) ∨ p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57997260187697847813189762019 : (((p5 → (False → p1)) → (p3 ∨ (p3 → ((p4 ∨ (((p5 ∨ p4) ∧ True) → (p4 ∧ ((False ∨ ((p5 → p2) ∨ p5)) ∨ False)))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51811245547088204516350826577 : (((p5 ∨ ((False ∧ (p3 → p4)) ∧ (((((p1 ∧ p4) ∨ p4) ∧ p2) ∧ p4) ∨ p4))) ∧ (((p5 → (p5 → p5)) ∧ (p3 ∨ p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1941438524810277455695956881 : ((((p3 ∧ (False ∧ ((False ∨ ((((p4 → False) → True) → p1) ∨ p3)) ∧ (False ∧ p1)))) ∨ p2) ∨ True) ∨ (p5 ∧ ((True → p1) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18015788973295430774715099828 : ((((p3 ∧ p1) ∧ ((((((p5 ∧ (p5 → p5)) ∧ (True → (p4 ∨ p5))) ∨ p3) → p5) ∨ p5) → p1)) ∨ (p4 → (p1 → (p1 ∨ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86700421452456305050403988825 : (((p5 ∧ ((True ∧ True) → (p1 ∧ (p4 ∨ p3)))) ∧ (((p5 ∨ p5) → ((p5 ∧ False) ∨ (True ∨ True))) → (p3 ∧ (p4 ∧ (p2 ∨ p4))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∨ p5) → ((p5 ∧ False) ∨ (True ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h6
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725617535953840097606751819841 : (((((p4 ∧ False) ∧ False) ∨ (p2 ∨ ((p5 ∧ ((p4 ∨ p4) → p2)) ∧ ((p2 → True) ∨ (((p5 → p2) ∨ p1) ∨ (False ∧ (p5 ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258038307614587792408383119351 : ((p4 ∨ p2) → ((p2 ∨ ((((p5 ∧ True) ∧ p5) ∧ ((False ∨ p4) ∨ False)) ∨ (((p3 ∨ (p3 → p3)) ∨ (False ∨ (p2 → p2))) ∨ p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112792954133401367114374315940 : (((((p5 → ((p4 → False) ∧ p5)) ∧ p3) ∧ (((p3 → p5) → (p4 ∨ (p2 ∨ p1))) → (p2 ∨ ((p3 → p3) ∨ p2)))) → p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159062958699427895562141485815 : ((p5 ∨ ((p2 → (True ∨ p5)) → ((p3 ∨ ((False ∨ (p3 ∧ p3)) ∨ ((p3 ∧ True) → p2))) ∨ p3))) ∨ (((p2 → (p5 ∧ True)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258295908179075410051521329061 : ((p5 ∨ True) → ((((p3 ∨ ((p2 ∧ False) ∨ True)) ∨ (((p1 ∨ p1) ∨ True) ∨ p5)) ∧ ((p5 ∨ p1) ∧ True)) ∨ ((True ∨ (True → p5)) ∨ p5))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303937343796566089525068728372 : (p1 ∨ ((((p4 ∨ p5) ∨ ((p3 ∨ p5) ∨ True)) ∧ (False ∧ ((p2 → ((False → False) ∨ True)) ∧ ((p2 ∧ (True ∨ p4)) ∨ (True ∨ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329684291372241204284837824117 : (True → ((p2 ∨ p4) → ((((p5 ∨ ((p1 ∨ p2) ∧ p4)) ∧ False) ∨ (((p3 → (True ∧ p3)) → ((p1 → p3) → (p3 ∨ p1))) ∨ p4)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326950346085603487979542364654 : (True → ((((p3 ∧ (((True → ((p5 ∨ p4) → (True → p4))) → ((p3 → p3) → (True ∨ p3))) → (p2 → False))) ∨ p2) ∨ (p2 → True)) ∨ p1)) := by
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
theorem thm_5_vars_59296024909851816208444095223 : (((p3 ∨ p5) ∨ ((((p3 ∨ ((p2 ∧ ((p5 ∧ p1) ∨ p3)) → (p3 ∧ p2))) ∨ p1) ∨ True) ∨ ((p3 ∨ p5) ∧ ((p3 ∧ True) ∨ True)))) ∨ p1) := by
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
theorem thm_5_vars_305175126018635593504040653722 : (p1 ∨ (((((p1 ∨ (True → False)) ∧ (p1 ∧ True)) → (p5 → p5)) ∧ ((p5 ∨ (p2 ∨ p5)) ∧ (p5 ∨ False))) ∨ (p3 → (p2 ∨ (p5 ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356624119958856430587761045931 : (p5 → ((((p3 ∧ (p5 ∨ p4)) ∨ p2) → (p1 ∨ p4)) ∨ (((p2 ∨ p2) ∧ True) → (p5 ∨ (((True → p4) → p5) ∨ (p2 → (p2 ∧ p4))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244183611402080334664925679714 : ((True ∧ p5) ∨ (((((p3 → ((p4 ∧ ((False ∧ (p2 ∧ p3)) ∨ p3)) ∨ (False → False))) → p4) ∨ (False → p1)) ∨ ((p2 ∧ True) ∨ p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615179508166040567457053059245 : ((((((((p3 → p3) ∧ p2) ∨ (p4 ∧ p3)) ∨ ((((p5 ∧ p3) ∧ p3) → True) → p5)) ∧ (p5 ∨ (((p1 ∧ False) → p5) ∧ p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171296185290296005108611946266 : (((((False ∨ (((p1 → True) ∧ (p4 → p5)) → (p1 → p5))) ∨ p1) ∧ p5) ∧ p2) ∨ ((False → ((p5 ∧ (p3 → (p5 → p3))) → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64057956938146715449577384023 : ((False ∨ (((p4 ∧ p5) ∧ ((p5 ∧ p3) ∧ (p1 ∧ ((p2 ∧ (p3 ∨ ((p1 → p1) → p4))) ∧ False)))) ∨ (((p4 → p4) ∨ p5) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_690083160477793018137565191660 : ((((p5 ∧ (p2 ∨ (((p5 ∨ p4) ∨ ((True → (p1 ∧ False)) ∧ p1)) ∧ (True ∨ p4)))) ∨ (((((p4 → p4) → p5) → p4) ∨ True) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261404137308132592494540992195 : ((p5 → p1) → (((True → p1) ∨ (p2 ∧ p4)) → ((p1 ∨ (p4 → True)) ∧ (p1 → (True ∧ (((((False ∨ p4) ∧ p4) → p5) ∨ p1) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111866340441257487454525837416 : (((((p1 ∧ (((((False → p3) → p4) ∧ (p4 ∨ (p2 ∧ p1))) → p3) ∨ p5)) ∧ True) ∨ ((p5 → p1) → (False → p1))) ∨ False) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646713387265083465658585117598 : ((((p2 → (((p1 → (p1 → ((False → p5) ∧ p3))) ∨ (((p5 ∧ p4) ∧ False) ∨ ((p5 ∧ p5) ∨ (p1 ∧ (p4 ∧ p3))))) ∨ p3)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135517769405514648809223080259 : (((((((p3 ∧ (True ∧ p4)) ∨ p4) ∨ p1) ∧ (((False ∧ p1) ∨ p2) → p3)) ∧ p2) ∧ (False → (p2 → (p5 ∨ True)))) ∨ (False → (False ∧ p3))) := by
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
theorem thm_5_vars_65644472515882550301850630783 : ((p4 ∨ (((p5 ∧ (False ∧ p2)) ∧ (p2 ∨ (((False ∨ (True → False)) ∧ ((True → p4) → p4)) ∨ (p3 → ((p4 ∧ p2) → p1))))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179049909963275479265246592686 : (((p3 → p1) → ((p4 ∧ (False → (False → (p3 → (False ∧ p1))))) ∧ p4)) ∨ (p1 → (p1 → (((p4 → p5) ∧ (True → p2)) ∨ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_337087851103653342753353293968 : (p1 → (((((False ∨ (p4 → ((False ∨ (p1 ∨ p1)) → p1))) ∨ p5) ∧ (True ∨ p4)) → (((False → p2) ∨ p4) → (True → p4))) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_510560900959336576884439942961 : ((((p3 → p3) ∧ (((p3 ∨ (((p5 ∧ (((False → p2) ∧ p2) → True)) ∧ p3) ∨ ((p2 ∨ p5) → ((p4 ∧ p3) ∨ True)))) → False) → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (((p5 ∧ (((False → p2) ∧ p2) → True)) ∧ p3) ∨ ((p2 ∨ p5) → ((p4 ∧ p3) ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151409978647990856907043108787 : ((((p4 ∧ (False → p3)) ∨ (p1 → ((((p4 → ((False ∧ p1) ∨ p3)) ∧ False) ∧ False) ∧ p5))) ∧ (p3 ∧ p4)) → ((p1 ∧ p2) ∨ (p5 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173341690309148363798598128377 : ((p2 → (True → ((p4 ∨ (((p2 ∨ (True ∨ p3)) → False) ∧ p1)) ∧ (True ∧ p1)))) ∨ (True ∨ ((p1 ∨ ((p3 → p4) ∧ p2)) → (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148307241100825661978018851220 : ((((False ∧ p3) → (p4 ∨ (False ∧ ((p2 → p3) ∧ (p1 ∧ (p1 → (p5 → False))))))) → ((p5 → p2) → p4)) ∨ ((True ∧ False) → (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231432088584356967066202411129 : (((p2 → False) ∨ True) → ((p1 → ((p5 ∨ False) ∧ p4)) ∨ ((p1 ∨ (True ∧ (True ∧ ((p3 ∧ True) ∨ p1)))) ∨ (((p2 → p1) ∨ p4) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167440320310502343106823196836 : (((p1 ∨ ((False → (p3 ∧ ((p2 ∧ False) → p4))) → (((p5 ∨ p2) ∧ False) → p1))) → p4) → ((p2 ∧ ((p2 ∧ (p5 → p4)) → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((False → (p3 ∧ ((p2 ∧ False) → p4))) → (((p5 ∨ p2) ∧ False) → p1))) := by
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
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137852306733493101663671360855 : ((p3 ∨ ((False ∧ p4) ∨ (((True → (((((p2 ∨ p1) → p3) → p5) → p1) ∨ p4)) ∧ p1) ∧ ((p3 ∨ p2) ∧ p5)))) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258901162898358527285009775245 : ((True → p2) → (((p4 ∧ True) → ((((False ∧ (p3 ∧ p5)) ∨ True) → (((p3 ∧ p4) ∧ (p3 → True)) ∨ p3)) ∧ False)) ∨ (p3 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_54003628193629689045144379384 : (((((((p1 ∨ (p4 ∧ p1)) ∧ True) ∨ False) → True) → p1) → (((p1 ∨ False) ∨ ((p4 ∧ p1) ∧ ((p4 ∨ p3) ∨ (p5 ∨ p3)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51217584448917584504196013482 : ((((True ∨ (((p1 → p2) ∧ p1) ∧ False)) ∧ ((((p3 ∧ p1) ∧ p4) ∧ (p4 ∨ p3)) ∨ p1)) ∨ ((((p2 → p1) ∧ p3) → p3) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308406573765512456063415461484 : (p2 ∨ (((((p2 ∨ ((p2 ∨ (False → (((p2 ∨ (p3 → p5)) → p1) → ((p1 ∨ p5) → (p3 ∨ True))))) ∨ True)) ∨ True) ∧ True) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186881273131837521039305122189 : ((((p4 ∧ False) → (p4 → p2)) → (False ∧ (p3 ∧ (p1 ∧ p1)))) → ((((p4 ∨ False) ∨ (p4 ∧ (p2 ∨ p1))) ∨ ((False → p2) ∧ p5)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ False) → (p4 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∧ False) → (p4 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h9
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113766801315218098531963608744 : ((((p4 ∨ (p1 ∨ (p2 → (True → p5)))) → ((((p2 ∨ p4) ∨ (False ∨ (p4 → p2))) ∨ (False ∨ True)) → True)) → (p2 ∧ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179646649528773809513767721647 : ((p5 → (((p4 ∧ (((p4 ∨ p2) ∧ (False ∧ p2)) ∧ p3)) ∨ p3) ∨ p5)) ∨ (p3 → (p3 ∨ (False → (p4 → (True ∨ (p1 ∨ (p5 ∨ p1)))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174843599040057797139277366971 : (((True ∨ p3) ∨ ((((p2 → False) → (True ∧ (p5 ∧ True))) ∨ True) ∨ (False ∧ p3))) → (p1 ∨ (p4 → (((p1 ∨ p1) → (p3 ∨ p1)) ∨ p3)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177631314343726811166581307728 : (((((((False ∨ p3) ∨ (p2 ∧ False)) ∧ False) ∧ (p3 ∧ p5)) ∧ False) ∧ p1) ∨ ((p5 ∧ (False ∨ p2)) ∨ (True ∨ ((True ∧ (True → False)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245431271549589226941948575274 : ((p2 ∧ p4) ∨ ((((p2 ∧ p3) ∧ p3) ∧ False) ∨ ((p1 → (p1 ∨ p5)) ∨ (p5 ∧ (((p2 ∧ False) → ((p2 → p3) ∧ p5)) → (p5 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127747098943957833734986909008 : ((True → ((((((((p1 → p5) ∧ (True ∨ (p1 ∨ False))) ∧ p3) ∨ p2) → (((p3 ∨ p1) → p4) → False)) → p5) ∨ True) → p5)) → (p3 ∨ p5)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((((p1 → p5) ∧ (True ∨ (p1 ∨ False))) ∧ p3) ∨ p2) → (((p3 ∨ p1) → p4) → False)) → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200226930707541727864217172555 : ((((True ∧ True) ∨ p5) → (False ∨ (p1 ∧ p1))) → ((p3 → False) → (((p4 ∨ ((p5 ∧ True) → p1)) ∨ p3) → (p2 ∨ (p2 ∨ (p1 ∨ p4)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((True ∧ True) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40503962327815095340359642010 : ((((p1 ∧ ((p2 → ((p4 ∧ (p3 ∨ (p3 ∧ True))) ∨ (((p2 ∨ (p5 ∨ p2)) ∧ p1) → (p2 ∧ (p3 ∨ p1))))) → False)) ∨ p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52296196415480846356376974853 : ((((((p3 ∨ p3) ∧ (p1 → ((p4 ∨ p3) → False))) ∧ (True ∧ p3)) ∧ p3) ∧ (((p1 ∨ (p4 → (p4 ∧ (p2 → p1)))) → p5) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609656388126745047297653185098 : (((((False ∨ ((False ∨ True) → (True → ((p4 ∧ ((True → (((p4 → False) → (p1 ∧ p4)) ∨ p4)) → False)) ∨ (p5 → p5))))) ∨ p1) ∨ p3) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158355717012525216352007155048 : (((False ∨ True) ∧ ((p5 → False) ∧ ((p4 → (p3 ∨ True)) ∧ (True ∧ (p4 ∨ (p5 ∧ (p2 ∧ p2))))))) ∨ (((p4 → p3) → True) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62769845951071034353785186707 : ((p4 ∧ ((((((((p4 → p5) ∧ p2) → ((p3 ∧ (p5 ∧ False)) ∧ p1)) → (p5 → False)) ∧ p3) → True) ∨ p4) → ((p2 ∨ p5) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177868230856353637787969909042 : ((((p3 ∨ (((((p2 → False) ∧ p1) ∧ p1) → False) ∨ p5)) ∨ p1) ∨ p1) ∨ ((True ∨ ((p1 → False) ∨ False)) ∨ ((p2 ∧ (p4 ∧ p1)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50351146899999817526182098970 : ((((p2 → (p5 ∧ (p4 ∨ p4))) ∧ ((p5 ∨ (p4 ∨ (True ∧ ((p4 ∨ p5) ∨ False)))) → (p2 → p1))) ∨ (((p1 ∧ p2) ∧ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197957499682110403811458568204 : (((p4 ∧ False) ∧ (((p1 ∧ p3) → True) → p1)) ∨ ((p3 ∨ True) ∨ ((p5 ∧ ((False ∨ ((True ∨ p1) ∨ p5)) → (p5 ∧ False))) → (p5 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178280941170749868695406697156 : ((((p4 ∨ False) → ((p1 ∨ ((True ∧ p3) ∨ True)) → True)) ∧ (p5 ∧ p3)) ∨ ((False ∨ (p5 ∧ p2)) → (p4 ∨ (((p3 ∧ True) ∨ p1) ∨ p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51419237590999199040802598948 : ((((p5 ∨ (False ∧ ((((p5 ∨ p1) ∧ p5) ∧ (True → (p3 → (p2 ∧ False)))) → p5))) → False) → (p2 ∨ (p3 ∨ (p5 → (p2 ∨ p4))))) ∨ p3) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ (False ∧ ((((p5 ∨ p1) ∧ p5) ∧ (True → (p3 → (p2 ∧ False)))) → p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722407907696537524040430297733 : (((((p5 ∧ p1) ∧ p3) ∧ (((p3 ∧ (p1 ∨ ((p1 ∧ (p2 ∧ p4)) ∧ False))) → (p1 ∨ (False ∧ (p3 ∨ (True ∨ (False ∨ p5)))))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255196544861536228368463566293 : ((p4 ∧ p4) → (((((p5 ∧ p3) ∨ p2) ∨ p3) → (True → (((p1 → (p3 ∨ p1)) ∧ (p2 ∧ False)) ∧ (p3 → p2)))) ∨ (False → (p1 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45553228477107245686463475237 : (((p2 ∨ ((False → (True ∧ (p1 → ((((False ∨ p2) → p1) ∧ (((p1 ∧ (p3 → p1)) ∨ False) → p5)) ∨ p5)))) ∨ (p1 → p1))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142421785394460494426278909857 : ((p4 ∧ (p2 ∧ ((p3 ∨ p2) ∧ ((p2 ∨ ((p2 ∧ p5) ∧ (((True → (False ∨ p1)) ∨ p5) ∧ (p3 ∨ p2)))) ∨ p3)))) → ((True → False) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h16.left
        let h20 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h22 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h23 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h24 := h2 h23
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h27 := h2 h26
            -- False on the left can always be used.
            apply False.elim h27
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h29 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h30 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h31 := h2 h30
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h33 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h34 := h2 h33
            -- False on the left can always be used.
            apply False.elim h34
    case inr h35 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h37 := h2 h36
      -- False on the left can always be used.
      apply False.elim h37
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h42 := h2 h41
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h44.left
        let h47 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h45.left
        let h49 := h45.right
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h49
          case inl h51 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h52 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h53 := h2 h52
            -- False on the left can always be used.
            apply False.elim h53
          case inr h54 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h55 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h56 := h2 h55
            -- False on the left can always be used.
            apply False.elim h56
        case inr h57 =>
          -- Disjunctions on the left can always be decomposed.
          cases h49
          case inl h58 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h59 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h60 := h2 h59
            -- False on the left can always be used.
            apply False.elim h60
          case inr h61 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h62 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h63 := h2 h62
            -- False on the left can always be used.
            apply False.elim h63
    case inr h64 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h65 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h66 := h2 h65
      -- False on the left can always be used.
      apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736327832603616174160706948229 : ((((False → p4) ∧ (p1 ∨ (((False ∨ p1) ∧ ((False → ((((p4 ∧ p5) ∨ (((True ∧ p3) → p2) ∨ p1)) ∧ p3) ∨ p5)) ∧ True)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48470112942504688267468135346 : (((((((p1 → False) ∨ (p4 ∧ False)) ∧ (True → (True → ((p1 ∨ p5) ∨ False)))) ∨ (p1 ∨ (True → p3))) ∧ p4) ∧ ((True → p3) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57316062936017390732215928198 : (((True ∧ (p4 → p2)) ∨ (((((((((False ∧ p2) ∨ p1) ∧ p4) ∧ (p5 ∨ False)) → False) ∧ True) → (p5 → (p5 → p3))) → p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185610136357351666585783914311 : ((True → ((((p2 ∧ (p1 → p5)) → p1) → (False ∧ p2)) ∨ p2)) ∨ (True ∨ (((p3 ∧ ((True ∨ (True ∨ (p1 → p1))) ∨ False)) → p2) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164636753002855668079636022454 : (((p3 ∨ (((True ∨ (p4 ∨ (p4 ∨ False))) → (p5 ∨ (p2 ∧ (p3 ∨ p2)))) → p1)) ∧ True) ∨ (((p5 → ((p5 → p2) → p2)) ∨ False) ∨ p4)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239150314702542892620257894698 : ((p2 ∨ True) ∧ (((p2 ∧ p1) ∨ (((p3 ∨ False) → False) → ((((p5 → p5) ∨ (False ∨ p4)) ∧ (((p1 ∧ False) → p2) ∧ p3)) → p1))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (p3 ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h16 := h1 h15
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59972238662275170391759793362 : (((False ∨ True) → ((True ∨ p2) → (p5 ∨ (p3 → (((((p3 → False) ∧ (p5 ∧ p2)) ∧ False) ∨ (True ∨ (p5 → (True ∨ True)))) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782447490013105292072755659237 : (((p3 ∨ ((((p1 ∨ ((p3 → p3) ∧ (((p4 ∨ (p1 ∨ True)) ∨ p1) → (False ∨ p3)))) → False) ∨ (p2 → ((True ∧ p3) ∨ False))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



