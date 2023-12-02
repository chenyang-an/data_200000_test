variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124431324924046550540598550250 : ((((p3 → ((False ∧ (p2 ∧ p4)) ∧ p2)) → False) → ((p5 → ((p3 ∧ (False → False)) ∨ ((p4 ∨ p2) → (p5 ∧ False)))) ∧ p1)) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315562756148329656475950049259 : (p3 ∨ ((True ∨ p4) ∧ (p2 → ((((p1 → p3) → p2) → ((True ∨ (p5 ∨ (p2 → ((p1 ∨ p3) ∧ p4)))) ∧ ((p2 ∨ p1) → p3))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670578392422423811290869300865 : (((((p4 ∨ p5) ∨ ((p3 → ((((p2 → p5) ∧ False) → (p5 ∨ p2)) → p4)) ∨ (p1 ∧ ((p3 ∨ False) → p4)))) ∨ ((p3 ∧ p1) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119296991062429338734104333013 : ((p3 → (((p4 ∧ ((p3 → p4) ∧ (p2 ∨ p3))) → ((((p4 ∨ p4) ∧ p5) → (p3 ∧ (p4 ∧ False))) → (p2 → p4))) → False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134425062926148687288316828735 : (((p4 → ((p4 → ((((p3 ∧ p3) ∧ ((True ∨ False) ∨ (p4 → p5))) ∧ p4) ∧ (p5 ∧ (p5 ∧ p3)))) → False)) ∨ False) ∨ (p4 → (p1 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37647117345875168485183345971 : (((((p2 → ((((True → False) ∧ (p2 ∨ ((p2 → p4) ∨ p5))) ∧ ((p1 ∧ (True → p4)) ∨ (False ∨ p2))) → False)) ∨ p3) → p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248045153748775274795388562294 : ((p1 ∨ p5) ∨ (((True ∨ True) → p5) ∨ ((True → ((((p1 → True) ∧ (p3 → p5)) ∨ True) ∨ ((True ∧ True) ∧ (p4 ∧ p3)))) ∧ (False → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228876866708064499578591772877 : ((p4 ∨ (False ∧ p3)) ∨ ((p1 → p4) ∨ (((p3 ∧ ((p3 → True) → p1)) ∨ p1) ∨ (((True ∧ (p5 ∧ ((p4 ∧ p5) ∧ p5))) → p4) → True)))) := by
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
theorem thm_5_vars_51137214169335250428699761734 : (((((False → ((p5 ∨ (p2 → p1)) → (((False ∨ (p3 ∨ p2)) ∨ True) → p1))) ∧ p3) → p5) ∨ (((p3 → True) → (True ∨ p3)) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57341300926156907423587575941 : (((p2 ∧ (p3 ∧ p2)) ∨ (False ∨ (((p5 ∧ (False → p4)) → ((p1 ∨ p2) → (True ∧ ((p4 ∨ (p3 → False)) ∧ False)))) ∧ (False ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67980075471429851576516585322 : ((p2 → ((p1 → (p4 ∧ p1)) → (((p4 ∧ (((False ∨ (p4 ∧ p3)) ∨ p5) ∨ (True ∨ p3))) ∨ (True → (False ∨ (False → p4)))) ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356052961765866651437089633181 : (p5 → ((p4 → (((((False ∨ False) ∨ p5) → p2) → (((False ∨ False) ∨ False) ∨ p2)) ∨ ((p1 ∧ True) ∧ p4))) ∨ ((p4 ∧ (p2 → False)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ False) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174479297714613000294072904506 : ((((False → p3) ∨ ((True ∨ p5) → True)) ∧ (True ∨ ((p3 ∨ (p1 ∨ True)) ∧ True))) → (p4 ∨ (True → (True ∨ (((p1 ∨ False) → p3) ∧ True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342305465233185482326839165090 : (p2 → ((p4 → (((True → (((True ∧ p5) ∧ ((p1 ∧ p5) → False)) → p4)) ∨ p5) → (p3 ∨ p3))) ∨ (((p4 ∧ p5) ∧ False) ∨ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78074390732734767167601841206 : (((True → (((((((True → p1) ∧ p5) → p4) → p5) ∧ (False → ((False → (p1 ∧ p1)) ∨ False))) ∨ p1) → ((p3 ∧ p1) → p1))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (((((((True → p1) ∧ p5) → p4) → p5) ∧ (False → ((False → (p1 ∧ p1)) ∨ False))) ∨ p1) → ((p3 ∧ p1) → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249193785823064261159031007517 : ((p4 ∨ p3) ∨ ((False ∨ (p3 ∨ (((p2 → False) ∧ p2) ∨ False))) ∨ ((p5 ∧ (((False ∧ p3) ∨ (p2 ∧ p4)) ∧ p1)) → (False → (p1 ∨ False))))) := by
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
theorem thm_5_vars_184111058870208061115261994290 : ((((p5 ∨ p3) ∨ ((False ∧ (False ∨ p3)) ∧ (p4 → p5))) ∨ True) ∨ (((((p3 ∧ p5) → True) ∧ p4) → (True ∧ ((p1 ∧ p2) ∧ p4))) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233276915722046874629001374706 : ((True ∨ (True ∨ False)) → (((p5 → ((((p4 ∧ (p2 ∧ (p1 ∧ p4))) ∨ True) ∧ p2) ∧ True)) ∨ (True ∨ (p4 → (p1 → (p1 → p5))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353413018499143344475141628297 : (p4 → (p1 ∨ (((False ∨ (p5 ∧ p5)) → (((p5 ∨ True) → ((p1 ∧ True) ∧ (True → (p4 → True)))) → (((False ∨ p2) ∨ p3) ∧ p3))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677769170164559952512935258966 : (((((p3 ∨ ((((p4 ∧ p5) → ((((p3 ∧ p3) ∧ False) ∨ False) ∨ (p1 ∧ p4))) → p4) → True)) → False) ∨ (False ∧ ((True ∨ p5) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198350112246762470471678631560 : ((p2 ∧ ((p3 ∨ p4) → ((p2 ∧ True) ∧ p2))) ∨ (p3 → (True ∧ (p4 ∨ (((p4 ∧ True) ∧ p5) ∨ ((p1 ∨ p1) → (p3 → (p3 → p3)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148538458037233468270992097046 : (((p1 ∨ ((True ∨ (p4 ∨ (p2 ∨ ((p3 → True) ∧ p3)))) → p1)) → (p3 ∨ (True → ((p2 ∧ p5) ∨ p3)))) ∨ ((p3 ∨ (p3 ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198380996159839724690710773546 : ((p3 ∧ ((p2 → (p3 ∧ p3)) ∨ (False → p5))) ∨ (False ∨ (p4 ∨ ((False ∨ p4) ∨ (p4 ∨ ((p3 → p2) → (False → ((False ∨ p2) ∧ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115277220564543379630318118684 : (((p4 ∨ ((p5 → (p2 → ((p3 ∨ p4) → p3))) → p3)) ∨ (p2 ∨ (p3 ∨ (p3 → (p4 → (((True ∨ p1) ∨ p4) ∧ p3)))))) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345601893993321262065554985266 : (p3 → (((p2 ∨ False) ∨ (((False ∨ (p5 ∨ True)) ∨ (p4 → ((False ∨ ((True → p3) → ((p4 → p2) ∧ (p3 → p4)))) ∨ False))) ∧ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189782691427350674832582741498 : ((True → ((((False ∨ p5) ∨ (True ∨ False)) ∨ p4) ∨ p3)) ∧ (((False ∧ (((False ∨ p1) → (p2 ∧ (p5 → p4))) ∧ p5)) ∧ p2) ∨ (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777075030925160705895220960141 : (((p1 ∨ ((p2 ∨ (((p5 ∨ ((p3 ∧ (p4 → (False ∨ (p2 ∧ (p4 ∧ (p3 ∧ p1)))))) → p1)) ∨ p2) → (True ∧ p2))) ∨ (False ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40812360587199788233691660999 : ((((p3 ∨ ((((p4 ∨ p2) → ((True → p5) ∨ ((((True ∨ p3) ∧ True) ∧ p2) ∧ p1))) ∧ (p2 ∨ (p1 ∨ p3))) → False)) → p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323389935582601222387923221105 : (p5 ∨ ((True → ((True → (((((p3 ∨ (p2 → p1)) ∧ (p3 ∧ ((p1 → (p1 → p4)) ∨ p3))) ∧ p4) ∨ p3) ∧ p4)) ∧ False)) → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112598433471456865431838138630 : ((((True ∨ (p4 → (p5 ∨ (p4 ∨ ((p3 → (p5 ∧ (p4 ∧ (p1 ∨ (p1 ∧ p5))))) ∨ (p3 ∨ p5)))))) ∧ (True ∨ p3)) → p4) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657669444520042131900841115424 : (((((p4 ∨ p5) → (((p5 → (False → False)) → True) → (((True → (True ∨ p1)) → (((p5 ∧ p5) → p4) ∨ True)) ∧ True))) ∨ (False → p1)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_683231724006536109150839227715 : ((((False ∨ ((((p3 → p2) ∨ (((p2 ∨ (p4 → (True ∨ p1))) → True) ∧ p5)) ∨ p1) → p2)) ∧ ((False → p3) → ((p2 ∧ p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783118429796497114412171198378 : (((p3 ∨ (((p4 ∨ (False ∧ ((((p2 → p3) ∨ (p5 ∧ (p1 ∨ (p4 ∧ p2)))) → (p2 → False)) → False))) ∧ p1) ∧ (p5 → (p2 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112820882554167690082171622820 : ((((p5 ∧ ((p3 → p1) → p5)) ∧ (p2 ∧ (((p1 → False) → (p5 ∧ (((p2 ∧ p1) ∧ (False → p2)) ∧ p5))) ∧ p3))) → p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185232301779681704207484682741 : ((False ∧ (((p3 → p1) ∨ p2) → (((False ∨ p5) ∨ p2) → p2))) ∨ (False ∨ ((False → False) → (((False ∨ p3) ∨ (p2 → p2)) ∨ (p5 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166835835639977622562769804248 : ((((False ∨ (((True ∧ p4) ∧ (p1 ∨ (True → p3))) ∧ ((True ∧ p1) → True))) ∨ p1) ∧ p3) → (p2 ∨ ((p1 ∨ (p1 ∧ False)) ∨ (p4 ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135903066572293811913165439223 : ((((False ∨ ((p2 → p4) ∧ ((p2 → (p5 ∧ p4)) → False))) → p5) → (True → ((((p4 ∧ p1) → p3) → True) ∧ p2))) ∨ ((False → p4) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141308929837018368730197131363 : (((True → (p2 ∧ (p1 ∧ False))) ∧ (False → (p5 → ((p2 ∨ p1) → (p3 ∨ ((p1 ∧ (p1 ∨ (False ∧ p2))) ∨ p1)))))) → (p5 ∧ (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315658773471076750607910798486 : (p3 ∨ ((p2 ∧ p5) ∨ (((p3 → (p2 → p5)) → (p3 → (True ∧ (p2 ∧ (False ∨ False))))) ∨ ((p4 → True) ∨ (((p4 ∧ p1) ∧ p3) ∨ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325035000906002207157040109946 : (p5 ∨ ((p5 ∧ True) → ((((p1 ∨ p4) → (p5 ∧ ((p3 ∧ (p5 → p5)) ∧ p5))) → p1) ∨ (p5 ∧ (((p2 ∨ False) → p5) ∨ (p5 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624922605276088109166116546235 : ((((p5 ∨ ((p5 ∨ p4) ∧ (p2 ∨ (((((p4 → False) ∧ p1) → (p1 → (p5 → p4))) ∨ ((False ∧ (p1 → p1)) → p1)) ∧ p2)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48349936574530233488153707644 : (((p3 ∨ ((p2 ∨ p4) ∧ ((p5 ∧ (True ∧ ((p3 → (p3 → (p1 → (p5 → False)))) ∧ p2))) → ((False ∨ p2) ∧ False)))) → (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682964526279682078597451608042 : (((((p2 → p4) ∨ ((p4 → False) ∨ (p5 ∨ ((p5 → (False ∨ ((False ∧ True) ∧ p5))) ∧ p2)))) ∧ ((((p2 ∧ False) → p2) ∨ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312227987173244106657244155564 : (p2 ∨ (p1 → ((((True ∨ p4) ∧ (((((p4 ∧ ((p3 → p4) ∧ (False ∧ (p3 ∧ (False ∨ p3))))) ∨ p3) ∨ p3) ∧ p3) ∧ True)) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312073355479935755493237838586 : (p2 ∨ (p5 ∨ ((p5 → (p3 → (p4 → (p2 ∧ p4)))) ∨ (((True → (False ∧ False)) ∨ ((False ∧ (p5 ∧ p5)) ∨ ((p2 ∨ p3) ∨ True))) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206075672089083262303587379024 : ((p3 ∧ ((p1 → p4) ∧ (False → p4))) ∨ (((p4 → (True → False)) ∧ (p2 ∨ False)) → ((((False ∧ p4) ∧ ((True ∧ p1) ∨ p5)) ∨ p3) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342009877454194875891453299231 : (p2 → ((p2 ∧ ((True → p5) → (False ∨ ((False ∨ (p5 ∧ p1)) ∨ ((((p3 ∨ False) → p2) ∧ True) ∧ (False ∧ True)))))) ∨ (p1 → (True ∨ True)))) := by
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
theorem thm_5_vars_321357056406905528470560928227 : (p4 ∨ (True → ((p1 → ((p1 ∧ p4) ∨ (p5 ∨ (((((p4 → False) ∨ p2) → (p5 ∨ p5)) ∧ p3) ∧ (((p3 ∨ False) ∨ p1) → p5))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23730602469343723540857756367 : ((((p2 ∧ p2) ∧ (p4 → p3)) ∨ (((p1 ∨ (p2 ∧ (((p2 ∨ (True → (p4 → False))) → (p5 → False)) → p5))) → (p3 ∨ p3)) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158356748232317247329564819654 : (((False ∨ p1) ∧ ((True ∧ p1) ∨ ((p3 ∧ (((p4 → False) ∨ p4) ∧ ((p3 → False) → p3))) ∨ False))) ∨ ((p3 → ((p2 → False) → True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590846921716771131526078995499 : (((((p4 ∨ ((p5 → (((p4 ∨ (p1 → (True ∧ ((p2 ∧ (p1 → (p2 ∨ p3))) → p1)))) → True) ∧ (p1 → p4))) → p4)) → False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659331829433506132245099839928 : ((((p5 → (p4 ∧ ((p2 ∨ ((((True ∨ False) → (p1 ∨ ((False ∨ p1) → (p4 ∧ p2)))) ∧ (True → True)) ∧ p1)) → p2))) ∨ (p2 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_615988733023521386789532372765 : ((((((True ∨ ((((False ∨ p1) ∨ p5) ∧ (p2 ∨ p3)) ∧ False)) ∨ (p1 ∨ True)) → (((p3 → (p5 → p2)) ∨ p4) ∨ (p3 ∨ True))) ∨ p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h6
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h6
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h6
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41599518852243012140491966724 : (((((True → (False ∧ ((p3 → False) ∨ True))) ∨ p2) ∨ (((((((p5 ∧ False) ∧ (p1 ∨ p4)) ∧ True) → p5) ∨ False) ∨ True) → False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932150955588120574512909154494 : (((((True → (True ∨ ((False ∧ p1) → p3))) → p1) ∧ (((False ∨ p2) ∧ p5) ∧ ((p3 ∨ (p4 ∧ p3)) ∧ ((p1 → (p5 ∧ p1)) ∨ p4)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740887723105962487044484915140 : ((((p3 ∨ p1) ∨ ((p2 → False) ∨ (((p3 ∨ (p5 ∨ (False → ((p1 ∧ ((True → (p2 ∨ p1)) ∨ False)) ∧ True)))) → (p2 → p3)) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53036195370717159262773048677 : ((((p1 → (True ∨ p2)) ∨ ((False ∨ ((True → p1) ∧ p2)) ∨ False)) ∧ ((True → ((p1 ∨ p3) ∧ False)) → ((False ∧ p1) ∧ (p1 → False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58857295823058125779006596521 : (((True ∧ p4) ∨ ((p3 ∨ (p2 ∧ (((p3 ∧ (p1 ∧ (p4 ∧ p4))) → (p4 ∧ (p2 ∨ p2))) ∨ False))) ∨ (False ∨ ((False → p3) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53145410190308402948612111445 : ((((((p3 ∨ (p4 ∧ (p3 ∨ (True ∨ False)))) ∧ p2) ∧ p1) ∨ True) ∨ ((p2 ∧ p1) ∨ ((((p3 ∧ True) → p3) ∧ p4) ∧ (p4 ∧ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336610865465510687767781454924 : (p1 → (((((((((p3 ∧ (p2 ∧ p4)) ∨ p2) → (p5 ∨ True)) → ((p1 → (p4 ∧ False)) → p3)) ∧ p1) ∨ p2) → False) ∧ (True → True)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((((p3 ∧ (p2 ∧ p4)) ∨ p2) → (p5 ∨ True)) → ((p1 → (p4 ∧ False)) → p3)) ∧ p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h5
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136400793458597781243708003078 : (((p4 ∨ ((False ∧ True) ∧ p4)) ∨ ((p1 ∨ p2) ∨ (False ∨ ((((p3 ∧ p1) → (p4 ∧ (p5 ∨ p5))) ∨ p2) ∨ True)))) ∨ (p4 → (p5 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_198620197196537828461587061040 : ((p2 ∨ (p4 ∨ (((False ∨ p2) → p2) ∧ p2))) ∨ ((p4 → ((p1 → p2) ∧ False)) ∨ (False → (True ∨ (((p1 → (p4 ∧ True)) → p2) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655455081217966669188713295040 : (((((p4 ∧ ((p4 ∧ ((p5 ∧ True) → (((False ∨ True) → p1) ∧ p4))) → ((True → (p1 → p3)) ∧ p3))) ∨ (False ∧ p5)) ∨ (p5 → p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_55236685792752765447179228598 : ((((p1 → (p2 → p4)) → (p5 → False)) ∨ ((p5 → (p3 ∨ (((p3 → ((p5 → p1) ∨ p5)) ∨ p5) → ((p5 ∧ p1) → p1)))) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116458902090538554123682296089 : (((True ∧ p5) ∧ ((p5 ∨ (False ∧ (((p1 ∧ False) ∧ True) ∨ (p2 ∨ ((p1 ∧ False) ∧ (p1 ∧ (p4 → p4))))))) ∧ (True → p5))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84741860710050650184451192622 : ((((((((False → p3) ∧ p2) ∧ p4) → p4) ∨ True) → ((False ∨ False) ∧ False)) ∧ (True ∨ ((p2 ∧ ((p2 ∨ True) → True)) ∨ (p2 → p2)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((((False → p3) ∧ p2) ∧ p4) → p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (((((False → p3) ∧ p2) ∧ p4) → p4) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (((((False → p3) ∧ p2) ∧ p4) → p4) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299190337479550202160785423505 : (False ∨ (((p3 ∧ (((((False → (p1 ∧ False)) ∨ ((p1 ∨ True) → ((p4 ∧ True) ∨ ((False ∨ p5) ∧ p5)))) ∨ p2) → True) ∨ p2)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224304641463197368992198063151 : ((False → (True ∨ p2)) ∧ (p5 ∨ (p1 ∨ ((False ∨ p1) → (((True ∨ p4) → (((p4 ∨ p3) → p3) ∧ p3)) → (p2 ∨ ((p4 ∧ True) ∨ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711342911363065448418321861078 : ((((p1 ∨ ((True → (p1 ∨ False)) ∧ p1)) ∧ ((p4 ∨ ((p3 ∨ p2) → ((True → p3) → ((p2 ∨ p3) ∧ (p1 ∧ (p1 ∧ p2)))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703499509867531111160455286992 : ((((True → (False ∧ ((p2 → ((p4 → p5) ∨ p1)) → False))) ∨ (((((p4 ∧ (p1 ∨ (p3 ∨ p2))) ∧ True) ∧ True) ∨ (p5 ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774857953722755556493527367372 : (((False ∨ (((p3 → (p4 ∨ p4)) ∧ p5) ∨ (p2 → (((p3 ∨ (p2 → (p2 ∨ False))) → ((False ∨ ((p1 ∨ True) ∨ p1)) ∧ False)) → p3)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (p2 → (p2 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184134479160645348565328087586 : (((p3 ∧ ((p4 ∨ (p5 → ((p2 → p3) ∧ p2))) ∨ p3)) ∨ True) ∨ (((True ∨ (p5 ∨ p5)) ∧ ((p4 → p4) → (p4 ∨ p3))) ∧ (p3 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351772695113564788503511278050 : (p4 → ((p2 ∨ (((p4 → p3) → False) ∨ (((p5 ∧ (p3 → False)) ∨ True) ∨ True))) → (((p2 ∨ p3) ∧ (False → p3)) → ((p2 → p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h20 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h21 := h4 h20
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h22 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h23 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h7
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h24 := h4 h23
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h25 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h26 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h27 := h4 h26
          -- One of the premise coincides with the conclusion.
          exact h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h37 =>
            -- One of the premise coincides with the conclusion.
            exact h28
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140285252373843700271695929794 : ((((True ∨ ((False ∨ (True → (p3 → (p1 ∨ p5)))) → p4)) → ((True ∧ False) ∧ (p5 → True))) ∧ ((p5 → p4) ∧ p2)) → (p3 ∧ (False ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ ((False ∨ (True → (p3 → (p1 ∨ p5)))) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h14 : (True ∨ ((False ∨ (True → (p3 → (p1 ∨ p5)))) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h15 := h10 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h22 : (True ∨ ((False ∨ (True → (p3 → (p1 ∨ p5)))) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h23 := h18 h22
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623969291194349451432947197920 : ((((p2 ∨ ((((((p3 → p5) ∧ False) ∨ ((p4 → (False ∧ ((True ∧ False) → (p1 → p1)))) → p5)) ∨ (False ∧ True)) ∨ p1) → p2)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180959261489431397862844145185 : (((True → False) ∧ (((p4 ∨ p2) ∨ (False → ((p5 → p1) ∧ p2))) ∨ p4)) → (p1 → ((p3 ∨ ((p4 → (False → False)) ∨ p1)) ∧ (True → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h26 := h20 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h29 := h20 h28
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h32 := h20 h31
      -- False on the left can always be used.
      apply False.elim h32
  case inr h33 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h34 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h35 := h20 h34
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706012627682361571546908353966 : (((((p2 ∨ p2) ∧ (((p2 ∨ p1) ∨ p3) ∧ p3)) ∧ (((False → (p4 → ((((False ∧ (True → p4)) ∨ p3) → False) → p3))) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172829882429625934173817001461 : ((True ∧ (p2 ∨ (((p1 ∧ p5) ∨ (((p5 → p5) ∧ p4) → (p5 ∨ p5))) → p1))) ∨ ((((p4 → p2) ∨ True) ∨ ((False ∧ False) → p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260769924680213993440570340257 : ((p3 → p5) → (((p1 ∧ True) ∧ ((((p3 ∧ (p3 → p1)) ∨ (((p3 ∨ p4) ∨ True) ∧ p4)) ∧ (p5 ∨ (p2 → True))) ∧ (False → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134215770585794406961361360868 : ((((True ∨ ((p4 ∧ False) → ((p2 → False) ∨ p1))) → (True ∧ ((((p3 ∧ p5) ∧ p1) → p2) ∧ (p5 → True)))) ∨ True) ∨ ((p4 ∨ False) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52867778846380350503424520779 : (((p2 ∧ (p5 ∧ (((p4 ∧ False) → (p2 ∨ p3)) → ((False → False) ∧ False)))) → (((p2 ∨ ((p3 ∨ p3) ∨ True)) ∨ p3) → (False ∧ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : ((p4 ∧ False) → (p2 ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h13 := h8 h9
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h1.left
          let h19 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h22 : ((p4 ∧ False) → (p2 ∨ p3)) := by
            -- Implications on the right can always be decomposed.
            intro h23
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- False on the left can always be used.
            apply False.elim h25
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h26 := h21 h22
          -- We need to get the right conjuct of h26 based on <expert-advice>.
          let h27 := h26.right
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h1.left
          let h30 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
          have h33 : ((p4 ∧ False) → (p2 ∨ p3)) := by
            -- Implications on the right can always be decomposed.
            intro h34
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- False on the left can always be used.
            apply False.elim h36
          -- We have shown the premise of h32, we can now drive its conclusion.
          let h37 := h32 h33
          -- We need to get the right conjuct of h37 based on <expert-advice>.
          let h38 := h37.right
          -- False on the left can always be used.
          apply False.elim h38
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h1.left
        let h41 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
        have h44 : ((p4 ∧ False) → (p2 ∨ p3)) := by
          -- Implications on the right can always be decomposed.
          intro h45
          -- Conjunctions on the left can always be decomposed.
          let h46 := h45.left
          let h47 := h45.right
          -- False on the left can always be used.
          apply False.elim h47
        -- We have shown the premise of h43, we can now drive its conclusion.
        let h48 := h43 h44
        -- We need to get the right conjuct of h48 based on <expert-advice>.
        let h49 := h48.right
        -- False on the left can always be used.
        apply False.elim h49
  case inr h50 =>
    -- Conjunctions on the left can always be decomposed.
    let h51 := h1.left
    let h52 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h53 := h52.left
    let h54 := h52.right
    -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
    have h55 : ((p4 ∧ False) → (p2 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h56
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- False on the left can always be used.
      apply False.elim h58
    -- We have shown the premise of h54, we can now drive its conclusion.
    let h59 := h54 h55
    -- We need to get the right conjuct of h59 based on <expert-advice>.
    let h60 := h59.right
    -- False on the left can always be used.
    apply False.elim h60
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h61 =>
    -- Disjunctions on the left can always be decomposed.
    cases h61
    case inl h62 =>
      -- Conjunctions on the left can always be decomposed.
      let h63 := h1.left
      let h64 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h65 := h64.left
      let h66 := h64.right
      -- One of the premise coincides with the conclusion.
      exact h65
    case inr h67 =>
      -- Disjunctions on the left can always be decomposed.
      cases h67
      case inl h68 =>
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h69 =>
          -- Conjunctions on the left can always be decomposed.
          let h70 := h1.left
          let h71 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h72 := h71.left
          let h73 := h71.right
          -- One of the premise coincides with the conclusion.
          exact h72
        case inr h74 =>
          -- Conjunctions on the left can always be decomposed.
          let h75 := h1.left
          let h76 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h77 := h76.left
          let h78 := h76.right
          -- One of the premise coincides with the conclusion.
          exact h77
      case inr h79 =>
        -- Conjunctions on the left can always be decomposed.
        let h80 := h1.left
        let h81 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h82 := h81.left
        let h83 := h81.right
        -- One of the premise coincides with the conclusion.
        exact h82
  case inr h84 =>
    -- Conjunctions on the left can always be decomposed.
    let h85 := h1.left
    let h86 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h87 := h86.left
    let h88 := h86.right
    -- One of the premise coincides with the conclusion.
    exact h87



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158362641902331226685225042112 : (((p2 ∨ True) ∧ ((p4 ∨ (True → ((p4 ∨ (False → True)) ∧ (((p4 ∨ False) ∧ p4) ∨ p4)))) ∧ p1)) ∨ ((True → ((p4 → p5) ∧ p4)) → p4)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258310588182661488743043037629 : ((p5 ∨ True) → ((p1 ∨ True) ∧ (p1 → (p4 ∨ (((((p5 → ((True ∧ True) ∨ p5)) → p1) ∧ p5) ∧ False) ∨ (p1 ∨ ((True ∨ p1) → p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147497129638696233137056116355 : (((False ∨ (((((False ∧ p1) ∧ p4) ∧ ((False → (((p2 ∨ p4) ∨ p4) ∨ True)) ∧ True)) ∧ False) ∧ p5)) ∨ True) ∨ (((p4 ∨ p1) ∧ p2) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37632307803649257589002098224 : (((((((True ∧ p5) ∨ (True → ((True → p5) → ((p5 ∨ p2) → ((p5 ∧ p1) → p1))))) ∧ ((p4 ∨ p4) → p5)) ∨ p5) → p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313008863582920046793565480677 : (p3 ∨ (((((False ∨ (True ∨ ((p3 → p3) ∨ (p5 ∨ p3)))) ∧ True) ∧ (((p5 ∧ ((p2 → p4) → True)) ∧ (p2 → True)) ∧ p3)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197579581159315639827498799487 : (((True ∧ ((p2 → False) ∧ False)) ∨ (p1 ∨ p5)) ∨ ((p3 ∨ ((p4 → False) ∧ ((p3 ∧ p3) ∨ (True ∧ ((p2 ∧ p1) → (p1 → p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41914356386890158028711927235 : (((((p3 ∨ p3) → p4) → ((p5 ∧ (False ∨ (((p5 → (p2 ∧ p3)) → (False ∨ p4)) ∧ (p1 ∧ (p1 ∧ p3))))) ∨ (p3 ∨ True))) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_232076177186863127752664202935 : (((p4 ∨ p2) → p3) → (((p5 ∨ p5) ∨ ((p1 → p2) → ((p1 ∧ ((p2 ∨ (p3 ∨ p2)) ∨ False)) → (p2 → p5)))) ∨ ((p5 ∨ p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261580269808523355170224146860 : ((p5 → p4) → ((((p2 ∨ ((p2 ∨ (True ∧ p2)) → True)) → True) → (p1 ∧ p4)) → (((True ∧ ((p4 ∧ p1) ∨ False)) ∨ p4) → (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 ∨ ((p2 ∨ (True ∧ p2)) → True)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h24 : ((p2 ∨ ((p2 ∨ (True ∧ p2)) → True)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h24
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950055398770668850261392936572 : (((((True ∨ p4) → p5) ∧ (p5 ∧ (p5 ∧ (p2 ∨ ((p5 → ((((p4 ∧ (p5 ∧ True)) ∨ p3) ∧ p5) ∨ p1)) → (p5 ∧ (p4 → p2))))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37560919211422738609701568317 : ((((p3 ∨ ((p1 → ((p4 → (False ∨ (p3 ∨ ((p5 ∨ p4) ∧ (True → (p3 ∧ (p1 → (p3 ∧ True)))))))) ∨ p4)) ∨ p1)) ∨ p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254354617259875703637930566973 : ((p2 ∧ p4) → (((((p1 → p4) ∧ ((p3 ∧ p5) → True)) → False) ∨ False) → ((p5 ∧ p3) ∨ (p1 ∨ ((p4 → (False ∧ False)) → (p3 ∧ p3)))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 → p4) ∧ ((p3 ∧ p5) → True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h6
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669662226116857947861534846297 : ((((((p4 ∨ (((((True ∧ True) ∨ (p1 ∨ p5)) ∨ (p5 → p5)) ∨ p5) ∧ p1)) ∨ p5) → (p2 ∧ (p3 ∨ p4))) ∨ (p5 ∨ (False → p2))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114426293329178935420683705983 : (((p2 ∧ (((((((p5 ∨ p4) ∨ (False ∨ False)) ∧ p2) ∨ p3) ∧ (True ∧ p1)) → False) ∨ p4)) ∨ ((p2 → (p4 → p1)) ∨ True)) ∨ (p5 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217735152477428162016051310493 : (((p2 ∧ (p2 ∨ p2)) → p1) → (((False → False) → (((((True ∧ True) ∨ False) ∧ p5) → p1) ∧ (p4 ∨ False))) ∨ (p4 → (p4 → (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305010674226497359829032286926 : (p1 ∨ (((p2 ∧ (False ∨ ((p1 ∨ p4) ∧ p1))) ∨ ((((p4 ∧ (p2 → True)) ∨ (p2 ∨ p1)) ∧ (p5 ∧ True)) → True)) ∨ (p4 ∨ (False ∧ p4)))) := by
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
theorem thm_5_vars_187154721733287519352091705444 : (((p2 → p1) ∨ ((((p1 ∧ p4) ∧ (False ∨ p2)) → p4) ∨ p4)) → ((((p2 ∨ p4) ∨ (p4 → p1)) → p1) ∨ ((p3 → (False → p5)) ∨ p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608776933021514918349834829796 : (((((((p1 ∧ ((p4 → ((p4 → p1) ∨ (p2 ∨ (p3 ∧ p2)))) → p3)) ∧ ((p5 ∨ p5) ∨ p4)) ∨ ((p4 ∨ p1) ∧ p5)) ∨ True) ∨ p3) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_234570041368154556521709419657 : ((p3 → (p5 ∧ True)) → (p5 ∨ ((((p2 → (((True → p3) ∨ p3) ∧ p3)) ∧ ((p1 → p1) ∨ (p2 → p5))) → (p4 ∨ p1)) → (p5 ∨ True)))) := by
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



