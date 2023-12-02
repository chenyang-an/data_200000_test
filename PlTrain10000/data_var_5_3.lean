variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147257084190407426195409755851 : ((((p1 → ((p4 ∧ (p4 ∨ ((p5 ∧ (False → (p5 → False))) → p2))) ∨ (p4 ∨ (p4 ∨ p3)))) ∧ p5) ∨ True) ∨ (p4 ∨ (p5 ∨ (p4 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37608411743157756665798355757 : ((((((p4 → ((p2 ∨ (True ∨ p4)) → ((p4 ∨ p3) ∨ (p4 → (True ∧ False))))) → ((False ∧ (p4 ∧ p1)) → p1)) ∧ p5) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191069038401927366317567585641 : (((p5 ∨ ((p3 → False) → p4)) → (p2 ∨ (p3 → p1))) ∨ (p4 ∨ ((p2 → ((((p4 ∧ (p3 ∨ p3)) ∨ p5) ∧ (p2 ∨ p1)) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263827666419195585487838836520 : (True ∧ ((((((True → ((p3 ∨ p3) ∧ p5)) ∧ p5) → p5) → (False → p4)) ∨ (p1 ∧ p3)) → (((p4 → (p1 ∧ p5)) → p1) ∨ (p4 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172650605993686822859715257239 : (((p3 ∨ p4) ∧ (((p5 ∨ ((((p5 ∧ True) ∧ p4) → p5) ∨ True)) ∧ p2) ∧ p5)) ∨ (p5 → ((p2 ∨ ((p2 → p1) ∧ (p1 ∨ True))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317607792737035396419533926755 : (p4 ∨ (((p3 ∨ ((p4 → p5) → ((p5 → (p3 ∨ (((p2 ∨ True) ∨ p1) ∧ p2))) ∨ ((p2 ∨ (True ∧ (p1 → True))) ∧ p5)))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46779161557484189662029905081 : (((p4 → (((p4 → (p1 → ((p3 → ((p2 ∨ (p3 ∧ (True → True))) ∨ (True → p2))) ∧ p5))) → (p4 → p1)) ∨ p1)) ∧ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721865240272997417540007792364 : ((((p4 ∨ ((p3 → p2) ∨ False)) → ((p3 ∨ ((p5 ∨ p2) ∨ False)) → (p5 ∨ ((p3 ∨ ((False ∧ p3) → (True ∧ False))) ∨ (False ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h14 =>
            -- False on the left can always be used.
            apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h19 =>
            -- False on the left can always be used.
            apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225738937058763997901273761941 : (((p4 → p2) ∧ p3) ∨ ((True → ((p4 → ((p3 ∨ (True → (p2 ∧ ((True → p3) ∨ p1)))) → (p2 ∨ p2))) ∧ p5)) → (p2 ∨ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258177668882956969313652933470 : ((p4 ∨ p4) → ((((p4 → (False ∨ p3)) → ((p5 ∧ True) ∨ p5)) ∨ (True ∧ (p4 → True))) ∨ ((p5 → ((p4 ∧ True) → p3)) → (p2 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305006989450879962998442627209 : (p1 ∨ ((((True ∧ p3) ∧ ((p5 ∧ (True → p4)) ∨ (p1 → p4))) ∨ ((p3 ∧ (p4 ∧ p2)) ∧ ((p5 ∨ p3) → True))) ∨ (p4 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_231425279211256668694725261905 : (((p1 → p5) ∨ p5) → ((((p4 ∧ (p2 → (p4 ∨ p2))) ∧ (((p2 → p4) ∨ ((p2 ∧ (True ∨ p3)) ∧ p1)) ∧ (p2 → p5))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54222707834612532831861095151 : (((((p1 ∨ (p5 → (p4 ∨ True))) → p5) → False) ∧ (((p4 ∨ (p1 ∨ (((p5 → p4) ∨ ((p5 ∨ False) ∨ p4)) → True))) ∧ p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159815990167634956777660514469 : (((False ∨ (((p4 ∨ p3) → (((True → p2) ∨ (p5 ∨ (p2 → (p5 ∨ p2)))) → False)) → p1)) ∨ False) → (p2 ∨ (True ∧ ((False ∧ p3) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303003622393562191126785047651 : (False ∨ (p1 → ((((((True → p2) ∧ ((p4 → p4) ∧ p5)) ∨ (p4 ∨ p2)) ∧ False) ∨ p4) ∨ ((False → ((True → (p4 ∧ False)) ∧ False)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137939181925006540048146568035 : ((p4 ∨ (p4 → ((p1 ∧ ((p3 ∧ p1) ∨ ((False ∨ p5) ∨ (False → p5)))) → ((p5 → (p2 → (False ∨ p4))) → False)))) ∨ ((p2 → True) ∧ True)) := by
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
theorem thm_5_vars_55517614056768889850475004541 : ((((p1 ∨ p2) ∨ ((p4 ∨ False) ∧ False)) → (((((((p4 → p5) → (p1 ∧ p4)) ∧ p2) ∨ (p1 ∨ (p4 ∨ p2))) ∨ p2) ∨ p5) ∨ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117043446844705601305041662856 : (((p3 ∨ p5) → ((((p2 → p3) ∨ False) → False) ∨ ((p2 ∧ ((True → ((((p5 ∨ p3) ∨ p4) ∨ p1) ∨ p3)) ∧ False)) → p1))) ∨ (p3 ∨ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313804724835316141239395846438 : (p3 ∨ (((((p1 ∧ (p4 ∧ (((False → p3) ∧ p3) ∨ p4))) ∧ ((p5 ∧ p3) ∨ (False ∧ False))) ∨ (p1 → (True ∨ True))) ∧ True) ∧ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183870979812588192531295760164 : ((((p1 ∧ ((p4 ∧ p1) ∨ p2)) → ((p3 → False) ∨ p5)) ∧ p5) ∨ (False → ((p2 ∨ p4) ∧ (((p2 ∧ (True → p3)) → (False ∧ p4)) ∨ p5)))) := by
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
theorem thm_5_vars_247831705436758782240304094025 : ((p1 ∨ p2) ∨ ((((True → (p4 ∨ (p2 ∨ p2))) ∧ ((p2 ∧ ((True → (((p2 ∧ True) → p5) ∧ (p2 → p3))) ∨ p1)) ∧ p3)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729189723876948775124585361719 : (((((p3 → True) ∧ p3) → ((p2 ∧ (((p4 → True) ∨ p4) ∧ ((p4 ∧ (p2 ∨ (True ∧ ((True → p2) ∨ True)))) → p5))) ∧ (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48319911929566791395259557949 : (((False ∨ (False → ((((p3 ∨ (p1 ∧ True)) ∧ False) → p4) ∧ ((False ∨ (p5 ∧ p2)) ∨ (p3 → (p1 → (p5 → p3))))))) → (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325090021247734414851119691118 : (p5 ∨ ((False → p4) → (p3 → (((p1 ∨ p2) ∨ (p4 → (p2 ∧ (True ∨ p5)))) → (p4 ∨ (((p5 ∧ ((p4 ∨ False) ∧ p4)) ∧ p4) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147159208599627036937469431485 : (((p4 ∧ ((p5 → ((p1 → p4) ∨ p1)) ∨ ((False ∧ (p3 ∧ (p4 ∧ ((p5 ∨ True) → p4)))) ∨ p5))) ∧ p4) ∨ (p4 → (p1 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_91154778517568469307366853039 : (((p5 → False) ∧ ((p1 ∧ (((p5 ∧ p5) ∧ p3) ∧ ((p1 ∧ (p4 ∧ True)) → ((p5 ∧ (p4 → (p4 ∨ (p1 ∨ p4)))) ∧ p1)))) ∧ p3)) → p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h14 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40548005540381912186796888531 : ((((True → ((False ∨ ((p1 ∧ p3) ∧ (True ∨ ((((p1 ∧ (p5 ∧ p4)) → (p1 ∨ (True → True))) ∨ p3) ∨ p4)))) → p5)) ∨ p5) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184776097268684601280349757082 : ((((p4 ∨ (p4 ∨ p1)) ∧ p5) ∨ ((p1 → (p2 ∨ False)) ∨ p1)) ∨ (((p3 ∨ False) ∧ p4) → (((p1 ∨ p2) → (p5 → (p3 ∨ True))) → p3))) := by
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
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330901899453110458341564542161 : (True → (p4 → (((p2 ∧ (((p3 ∧ ((p4 → (False → (False → ((p3 ∧ (p2 ∧ p4)) ∧ (p5 ∧ p5))))) → p5)) ∧ p5) ∨ p2)) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63450756784607102096437026832 : ((p5 ∧ (p5 → ((((False ∧ (True ∧ (p1 ∨ (False → (((p2 ∨ (p5 ∨ ((True → p4) ∧ p1))) ∧ p2) ∨ True))))) → p4) → p3) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134930042376161999417772336177 : (((((p1 ∧ ((False ∨ p2) ∧ (p5 ∧ False))) ∨ (p3 ∨ ((False ∧ (p3 ∨ p2)) ∨ (p4 ∨ p3)))) → p2) ∧ (p3 ∧ False)) ∨ (False → (p1 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41232800233357665049304906372 : ((((True ∧ (((p1 → (p2 → ((p3 → (p3 ∧ p3)) → (p3 ∨ p3)))) ∨ True) ∧ (True → p2))) ∧ ((p1 ∨ p5) → (p3 ∨ p4))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45783576681345244483012638556 : (((p1 → ((p3 → (((p1 ∧ ((((p5 → (p1 ∨ (p4 → (p5 → (p4 ∨ p1))))) → True) → p1) ∨ False)) → True) ∧ p4)) ∨ p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200143233499694938994845102402 : ((((p5 ∧ True) ∧ p1) ∨ (p5 → (p3 → True))) → ((((((((p2 → p1) ∧ p1) ∨ p2) → p4) ∨ p3) → p1) → (p4 → p1)) ∨ (p4 → p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (((((p2 → p1) ∧ p1) ∨ p2) → p4) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h17 := h9 h11
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654417360662685970086226112427 : (((((((p2 ∧ p4) ∨ (p5 ∨ p3)) → ((((True ∨ (p3 ∧ (True ∧ ((p1 ∧ False) ∨ False)))) → False) → p4) → p1)) ∨ p1) ∨ (False → p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_111899454811700672993274857763 : ((((((p4 ∧ ((False → p3) ∨ ((p1 → True) → (p3 → p1)))) ∨ p3) ∨ False) → (p1 ∨ ((p2 ∨ (p3 ∧ p3)) ∨ p3))) ∨ True) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65745131471729704073741941300 : ((p4 ∨ ((((p2 ∨ ((((p1 → (p2 ∨ p1)) ∨ True) ∧ True) ∧ (p3 ∨ False))) ∨ (False ∨ (p1 ∨ True))) ∧ p4) → ((p4 → p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113504893805573891059555475900 : (((((p5 ∨ ((False ∨ (((True → p1) ∨ True) ∨ (p3 → False))) → p3)) ∧ p2) ∨ ((p2 ∨ True) ∨ (p1 ∧ p3))) ∨ (True ∧ p5)) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_301890692573823212908024102153 : (False ∨ ((True ∧ p5) → (((((((True → (p5 ∨ ((p4 ∨ p5) ∧ p3))) ∧ True) ∧ p5) ∨ p2) → (p1 ∧ (p3 ∧ False))) ∨ p5) ∧ (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42434156193759859705921557105 : (((p5 ∧ ((p2 → p5) ∨ (p1 ∨ ((p5 ∧ ((p3 ∨ ((False ∨ ((p3 ∧ p5) → p2)) → p2)) ∨ True)) → (p4 ∨ (p3 → p1)))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306201992269447542168444810056 : (p1 ∨ ((p3 → (p3 ∧ p1)) ∨ ((((p4 → ((((False → p5) → ((True ∧ True) → False)) ∨ (p5 ∧ True)) ∧ (True ∨ p3))) ∧ p1) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706386674896468325216104553717 : ((((False ∨ ((p3 ∧ p4) ∨ ((False ∨ p1) ∨ p2))) ∧ ((((((False → (p4 → True)) → p3) ∨ p2) ∨ p4) ∧ False) ∨ (p5 → (p1 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19188540939129688913498400381 : (((p3 ∧ (p3 → (((((p3 → (p1 ∧ (True ∧ False))) ∨ p3) ∧ p3) → False) ∧ (False → False)))) → ((p1 ∧ p4) ∨ ((True ∧ False) ∧ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((p3 → (p1 ∧ (True ∧ False))) ∨ p3) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326170396837963509629320258100 : (p5 ∨ (p2 → ((((((p2 ∧ p3) ∨ p2) ∧ ((p5 → False) ∧ (False → p4))) ∧ ((p4 → p5) → p3)) ∧ ((p3 ∧ p4) → p2)) ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135746851542806398308472763341 : (((((p4 ∧ p5) ∨ False) ∧ ((p5 → (False ∧ False)) → ((False ∧ p1) ∨ p3))) ∨ ((False → False) ∧ ((p2 ∨ True) ∧ p4))) ∨ (p5 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53735185413337334045476545117 : (((p3 → ((p2 ∧ ((p3 ∧ (False → True)) → p3)) → p3)) ∧ (p2 ∨ ((p5 ∨ (p2 ∧ (((True ∨ False) ∧ (p4 → p3)) ∨ p2))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67868060436178987707224480977 : ((p2 → ((((p4 ∨ p3) ∨ p1) → ((p4 ∧ ((p4 → p5) ∨ (True ∧ False))) → ((False → (p3 ∨ p5)) → p1))) ∨ ((p4 → True) ∧ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167813968602688913265481503359 : (((((p4 ∨ p5) ∧ p1) ∨ (p3 ∨ ((p2 ∨ p4) ∧ False))) ∧ (p1 → ((p2 ∧ p5) ∧ False))) → (p3 ∨ ((True → False) ∨ (p1 ∧ (p2 ∨ p2))))) := by
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
    cases h5
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257633935051549267883286701236 : ((p3 ∨ p2) → ((p1 → (p4 ∨ ((p3 ∨ (p3 → (p2 ∧ False))) ∧ False))) ∨ ((((p5 → p2) ∧ p5) → (((p1 ∧ p2) ∨ p5) ∨ False)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23178224722695889488680018778 : (((True ∧ ((p2 → p5) → (False ∧ p5))) → ((((True ∧ (p4 ∨ p1)) → ((((p4 ∧ p1) → p1) → False) ∨ (p1 ∧ p2))) ∨ p2) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_323893364967302822831334458447 : (p5 ∨ (((p2 → (p2 → ((((((p2 → True) ∨ p1) ∨ p5) ∨ p4) ∨ p2) → p1))) → p1) ∨ ((((p1 → True) ∧ True) ∨ False) ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139456988003103311046626972736 : (((((p5 ∧ (((p4 ∧ ((p5 ∧ p1) ∨ p2)) → ((False ∨ False) ∨ p2)) ∧ p2)) → (p3 ∨ (p4 ∨ p4))) ∨ True) → False) → (p4 ∨ (False ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (((p4 ∧ ((p5 ∧ p1) ∨ p2)) → ((False ∨ False) ∨ p2)) ∧ p2)) → (p3 ∨ (p4 ∨ p4))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207576548303543713068210300008 : ((((False ∨ (True ∧ True)) ∨ True) → False) → ((p3 → ((False ∧ (((p5 → p5) → p2) → p2)) ∧ (p2 → False))) ∨ ((p3 ∧ p5) ∨ (p2 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (True ∧ True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56671223807077771867371950064 : ((((p1 → False) ∧ p4) ∧ (((False ∧ True) ∨ (p3 ∧ ((p1 ∨ (p5 ∨ p4)) ∧ True))) ∧ ((p2 ∨ p5) ∨ (((p3 ∨ False) ∧ True) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147104364463456529027555196065 : (((((p3 ∨ p2) → p3) → ((((False → p4) ∧ p5) → (p1 ∨ p5)) ∧ ((p5 → False) ∧ (False → False)))) ∧ p1) ∨ (p4 → (p1 → (p4 ∨ False)))) := by
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
theorem thm_5_vars_117161997355520681526032266128 : ((True ∧ (((p2 ∧ p3) → ((True → ((p4 → ((((p2 ∨ p1) ∨ p4) ∨ (p3 → p1)) ∨ p4)) → p1)) → (p4 ∨ False))) ∨ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25552261904297137911108555775 : (((p5 ∨ (p1 ∧ p5)) → (p1 → (((True → (p3 ∨ ((False ∨ ((False → False) ∨ p5)) → (p4 ∧ (True ∨ p5))))) ∧ True) ∨ (p4 ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471494587987306625053100510841 : ((((((p1 ∨ (p1 ∨ ((False ∧ (True ∧ p4)) → p2))) → p1) ∨ p5) ∨ (((p2 → True) → p2) → (False → ((False ∧ p2) → (p1 ∧ True))))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78837270880547895114211178404 : ((((True → (True ∧ p2)) ∧ (((False ∨ p3) ∨ False) ∨ ((p1 → (p1 → (p1 → False))) ∨ ((True ∧ (p1 ∨ p5)) → p2)))) ∧ (p3 ∨ p3)) → p2) := by
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
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h10 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h11 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h12 := h4 h11
          -- We need to get the right conjuct of h12 based on <expert-advice>.
          let h13 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h16 := h4 h15
          -- We need to get the right conjuct of h16 based on <expert-advice>.
          let h17 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h27 := h4 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h30 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h31
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h36 := h4 h35
        -- We need to get the right conjuct of h36 based on <expert-advice>.
        let h37 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623466222987462787325170721468 : ((((False ∨ ((p5 ∨ (((p2 → False) ∧ (((p1 ∨ p5) ∨ p4) → (False → ((p4 ∨ p1) ∨ p5)))) ∧ p2)) ∧ ((p1 ∧ p2) → p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_219306111391607096320546957243 : ((p2 ∨ ((True ∧ p4) → p2)) → ((((((((p4 → (p2 → p5)) → p1) → True) ∧ ((p1 ∧ p3) → p2)) ∨ True) → p2) ∧ p3) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347128823615489687169929193069 : (p3 → ((((p4 ∨ (p2 ∨ p2)) ∨ (True ∨ (p4 ∨ ((False ∨ p1) ∧ p5)))) ∨ p1) → (p4 ∨ (p3 ∧ ((False ∧ (p1 → (p1 ∨ False))) → False))))) := by
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
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Implications on the right can always be decomposed.
          intro h8
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- False on the left can always be used.
          apply False.elim h9
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Implications on the right can always be decomposed.
          intro h12
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h25 =>
            -- False on the left can always be used.
            apply False.elim h25
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- One of the premise coincides with the conclusion.
            exact h1
            -- Implications on the right can always be decomposed.
            intro h27
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- False on the left can always be used.
            apply False.elim h28
  case inr h30 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h31
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204104670960536100701380843913 : (((((False ∨ p5) ∧ p5) ∧ p2) ∧ False) ∨ (False ∨ (True ∨ (((p4 ∨ p5) ∧ True) ∧ ((p5 ∨ True) → ((True → p3) → ((p3 ∧ p2) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747486769000120100868808475024 : ((((True → p1) → (((p2 ∧ (((False → (p1 ∧ p1)) → ((False ∧ p3) ∧ p3)) ∨ ((p2 → p4) ∧ (p2 → p1)))) → True) → (p4 ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158121132675945586364956418420 : (((p5 ∨ ((p5 ∨ True) ∨ p2)) ∧ (((p1 ∧ ((((p5 ∧ p3) ∨ p5) ∧ True) ∨ p3)) ∧ p3) ∨ p4)) ∨ (((p4 → True) → False) → (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338822208888909189018130233128 : (p1 → ((p4 ∨ p2) ∨ ((p3 ∧ ((p1 ∨ (p1 ∨ (p3 ∧ p3))) ∧ ((p5 ∨ p2) ∧ True))) ∨ ((p3 ∨ (p4 ∨ p1)) → ((p3 ∧ p2) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357249826285021214257973229829 : (p5 → ((False ∧ True) ∨ ((((p1 ∧ ((p2 ∨ (p4 → p2)) ∨ (((p5 ∨ True) ∧ (False ∨ (p2 ∧ (p2 → p4)))) → p1))) → p2) ∧ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172467567883413650589551256293 : (((p4 → (p3 ∨ (p1 ∨ False))) ∨ ((p3 → (((False → p4) ∨ p1) → p1)) ∧ False)) ∨ ((p5 ∧ (False ∧ True)) → ((p1 → p2) → (p1 → True)))) := by
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
theorem thm_5_vars_347099750327630337748449004169 : (p3 → (((p4 ∨ (False ∧ (((False → ((p1 ∨ True) ∨ p2)) → p1) ∨ p4))) ∨ True) ∨ (p2 → (((p5 ∧ ((p2 ∧ p2) ∨ p2)) → p2) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327063765088905277058370343377 : (True → ((((p4 ∧ False) → (p1 ∧ p2)) ∧ (((p2 ∨ (((p5 ∧ p1) ∨ p3) ∧ p4)) → ((p1 → p3) ∨ ((p2 ∧ False) → p5))) ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721908160378426905584446769695 : ((((p5 ∨ ((p1 → p2) ∨ p1)) → (((((True ∨ True) ∧ False) ∧ True) → (p4 ∧ (False → p2))) ∧ (p3 ∧ ((p4 ∧ True) ∧ (False ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44675324045898233758602724556 : (((((p1 ∧ (p3 ∨ p1)) ∧ (p2 ∨ p4)) → ((p4 ∧ ((((True ∨ (p4 → p1)) → ((True → False) → p3)) ∧ False) → p5)) ∧ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115618852530888715409766392003 : (((p1 → ((True → False) ∧ (p3 → p3))) ∧ (((False ∧ (False ∨ p5)) ∧ (((False ∨ True) ∧ (p3 ∨ p1)) ∨ p5)) ∨ (p3 → p2))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65214215069067570009273829892 : ((p3 ∨ ((((p1 → (p4 ∨ ((True ∧ ((p4 → False) ∧ p1)) → p3))) → p4) ∨ (p3 ∨ ((((True ∧ p3) → p4) ∧ p1) ∧ p2))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56549115299580815234940361731 : (((p2 ∨ (p5 → (True ∨ True))) → ((True → p2) ∨ ((((((p1 → p2) ∧ p3) ∨ (p4 ∨ ((p4 → p4) → True))) ∨ p4) ∨ p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304989730517935190315117004534 : (p1 ∨ ((((((p2 ∧ (((True → (p3 ∨ (p4 ∧ p2))) ∨ p3) → p3)) → p2) ∨ True) → (p1 ∨ (True → p2))) → False) ∨ (p3 → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38079056780475240967939421241 : (((((p2 ∨ p2) ∨ (p4 → (((True ∧ True) → (p1 ∧ (p1 ∨ (p2 → (((p1 ∨ p2) → p4) ∨ p3))))) → p3))) → (p1 ∨ p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225231053705544379119124999459 : (((p5 ∧ p3) ∧ p1) ∨ (((p1 ∨ True) → (p1 ∧ (((p2 ∧ ((False → (False ∨ (p1 ∨ p5))) ∧ p3)) ∧ (p5 → False)) ∧ (False → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730173884898441463633748856877 : (((((True → p1) → p2) → (((p3 ∨ (p1 → p3)) → (p5 → (False ∧ p3))) → ((True → (True ∧ (p2 → p1))) ∨ ((p5 ∧ False) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154980941691403146488930774023 : (((p5 ∧ ((False ∨ True) → ((p4 → ((False ∧ p4) ∨ (False → p1))) ∧ p1))) → (p1 ∨ (p5 ∨ p2))) ∧ ((True → False) → (p4 ∧ (p2 ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254853400645795744678120893831 : ((p3 ∧ p5) → (True ∧ ((((p4 ∧ (p2 → p3)) → (p3 ∧ (True ∨ (p4 → (p3 → p5))))) ∧ p1) → ((((p2 → p3) → p4) ∧ p3) → p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : (p2 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h12 := h4 h10
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66737502342125204799143036176 : ((True → ((p4 → True) → (((((p5 ∨ p5) ∨ p1) → (((False → p4) → p3) → (False → p1))) → p4) ∨ (p5 → (p2 → (p5 → p5)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199724812222833561279066280704 : (((True ∨ ((p4 ∨ p1) → (p2 ∧ p4))) → True) → ((((p5 ∨ p5) ∨ (p1 → False)) ∨ (((p3 → (False ∨ (p3 ∨ True))) ∨ p1) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753260353648080356443424628961 : (((False ∧ ((p1 ∧ ((((p5 → ((p5 ∨ False) → p3)) ∧ (p2 ∨ ((True ∨ (p1 → p3)) ∨ (p1 ∧ p4)))) → p3) ∧ p1)) ∨ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936962510798647786734926313907 : ((((((p4 → p4) ∨ (p4 ∧ True)) → False) ∧ (p4 → (((p4 → (p1 ∧ p5)) ∧ (p4 → ((p4 ∧ p2) → p5))) → ((p5 ∧ p3) ∨ p2)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p4) ∨ (p4 ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352009746436648069477675755959 : (p4 → ((False ∧ (((p3 → p1) ∨ p5) ∧ (False ∨ p4))) ∨ (((p1 ∨ p5) → (p3 ∨ (((p3 ∧ p1) → p1) ∨ p1))) ∨ ((p1 ∨ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690943728608239985776524654090 : ((((((p4 → p2) ∨ ((p1 ∧ (p3 ∨ False)) ∧ ((p2 ∨ False) → p3))) ∨ (True ∨ p4)) → (p3 ∨ (p2 → (False ∨ (p4 → (p2 → p2)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115908130009656776259546929601 : ((((p2 ∧ p4) ∧ (False ∨ p2)) ∨ ((((((p2 ∧ False) → (False ∨ True)) ∨ p2) ∨ False) → p2) ∨ ((p1 ∨ p4) → (True ∨ p5)))) ∨ (True ∧ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146297967734640829640240350753 : ((False ∨ (((((p3 → False) ∨ ((p5 ∧ True) ∧ ((p5 → (True ∧ (p1 → p3))) ∨ p5))) ∧ False) ∧ p5) ∨ True)) ∧ (p4 → (p4 ∨ (p5 ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186793167061816368871039469070 : ((((True ∧ (p3 ∨ p4)) → p5) ∧ (((False → p2) ∧ p5) ∨ p1)) → (((p2 ∧ (p4 ∧ p2)) → p5) ∨ (p1 ∨ (False → (p5 ∧ (p3 → p4)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213400178198804898706687268850 : (((p1 ∨ (p2 ∧ p3)) ∧ p1) ∨ ((((p4 ∧ (p1 ∧ (False ∨ (True ∨ p4)))) ∧ p1) ∨ p4) ∨ (True ∨ (p1 ∨ ((True → False) ∨ (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356035108239815337001013824922 : (p5 → (((p5 ∨ (p1 ∧ p3)) ∧ ((((p3 → True) ∧ p5) → p5) ∧ (((False ∨ p4) ∨ (p4 ∨ p4)) → p1))) ∨ ((p3 ∨ (False ∨ True)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_348097950688468963065927369092 : (p3 → ((p2 → p4) ∨ ((True ∧ ((False ∧ (p1 ∧ ((p1 ∨ p3) ∨ p3))) ∨ ((p4 ∨ p1) ∧ (p2 ∨ (p2 ∨ p3))))) ∨ ((p4 ∨ False) → True)))) := by
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
theorem thm_5_vars_342023345865498033472247651937 : (p2 → ((p3 → (p1 ∨ (((p4 → (p1 ∨ ((((p3 ∨ (True ∧ p4)) → p1) ∨ p3) → p3))) → p4) ∧ (p1 ∨ True)))) ∨ (p4 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_258895104456862773673275682054 : ((True → p2) → (((((p1 ∨ p5) ∨ (p4 ∨ (((p2 → (((False → p5) → p2) ∧ p3)) → (p1 → p4)) → p4))) ∨ p4) ∨ p2) ∧ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669813358210979097025169786345 : (((((p3 → (((True ∨ (p5 ∧ (((p4 → p1) → p2) → p5))) ∨ False) → p2)) → (((p5 → False) ∨ True) → p2)) ∨ ((p1 → True) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_78743915220729808750918270611 : ((((True → (((True ∨ p5) ∧ ((p1 ∧ p4) ∧ p5)) ∨ False)) ∧ (p3 ∧ ((((p1 ∨ True) ∨ (p5 ∧ p2)) ∧ p4) → p4))) ∧ (p4 ∨ True)) → p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h14.left
        let h22 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h21.left
        let h24 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357441872943969015358157233543 : (p5 → ((True → False) → ((p4 ∧ ((((p2 ∨ (p5 ∨ ((p5 → p5) → p3))) ∧ False) ∧ (p3 ∧ (p5 ∨ (False ∨ p5)))) ∨ (p4 ∧ False))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683236441959359234409908699527 : ((((False ∨ ((p1 → ((p4 ∨ ((p1 ∨ True) → p1)) ∨ (p4 ∧ False))) ∧ ((p5 ∨ p3) ∧ p1))) ∧ ((p1 ∨ p1) ∨ ((False ∧ p4) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41094974822267249699287746687 : ((((((((p1 ∨ ((p4 ∧ ((p1 ∨ p1) → p4)) ∨ p4)) ∧ p2) ∧ p5) ∨ (p4 → p1)) → (False ∨ p5)) ∧ (p5 ∧ (p1 ∧ False))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



