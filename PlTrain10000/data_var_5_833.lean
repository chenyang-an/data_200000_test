variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147776808994766630145054877675 : ((((True → p3) ∨ ((p5 ∨ (p4 ∧ (p1 → (p1 ∧ True)))) ∧ (((p1 ∨ p5) → p5) → (p4 ∧ p3)))) → p2) ∨ (p5 → ((p5 ∨ p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57579144745893129713912658616 : ((((p3 ∨ p1) ∧ p4) → ((((p2 ∧ (p5 ∨ (p5 → (p2 ∨ p3)))) ∧ p4) ∨ (p3 → (True ∧ ((p4 ∧ (p5 ∧ True)) ∨ p4)))) ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226540594596709181064201053450 : (((p3 → p5) ∨ False) ∨ ((p1 ∨ (((p3 ∨ ((p4 ∧ p3) → (True ∨ (True ∧ (p1 ∧ p5))))) → ((p3 ∨ p5) ∨ p3)) → p3)) → (p5 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315319365724569294557192291518 : (p3 ∨ ((p5 → ((p2 ∧ p1) ∧ p1)) → (((p3 ∧ (p1 ∨ p1)) ∨ True) ∨ ((((p1 ∧ p3) ∧ (p2 ∧ p3)) ∨ (p4 ∧ (p4 ∨ p5))) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58845546356874869998530847485 : (((True ∧ p2) ∨ (((p5 → (p1 ∧ ((p1 → (((True ∧ (True → (p5 ∨ (p2 ∨ True)))) ∧ p5) ∨ p1)) → p2))) ∧ p1) → (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115701398176845405190068857740 : (((((p3 ∨ (p4 → False)) ∧ p3) ∧ p1) → (((p4 ∧ ((p2 → True) ∨ (((p2 ∧ p5) ∨ p4) → p4))) → p2) ∧ (p3 ∨ False))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228040966439574302938184189019 : ((p4 ∧ (True ∧ True)) ∨ (((p3 ∧ ((((((True → (p2 → False)) ∧ True) ∨ p5) → (p5 ∧ ((p3 ∨ p3) ∨ False))) ∨ p1) → p1)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205707233310215382028446778358 : (((p1 → False) ∨ (p4 ∨ (p2 ∧ p5))) ∨ ((((p2 ∨ (True ∧ (((p1 ∧ False) ∧ False) → p1))) ∨ ((p5 → (p3 → False)) ∨ p5)) ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116598210637236191054163922987 : (((p5 ∨ p2) ∧ (p4 ∧ ((((p2 ∧ p4) ∧ ((p1 ∧ (((((p3 ∨ p4) → False) ∧ p1) ∧ p4) → p2)) → True)) → False) ∨ True))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215336028775399432732077768184 : ((p1 ∧ (p4 ∨ (False → p1))) ∨ (((False ∨ ((p3 → False) ∨ ((((p4 ∧ p5) ∨ p5) ∨ p3) ∧ ((p4 ∨ p3) → p1)))) ∧ False) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_904234466401572796835662744070 : ((((((p2 ∨ ((p4 → p1) ∧ p1)) → (((p2 ∧ ((False ∨ p5) ∧ (True ∨ True))) ∨ p2) ∨ True)) → p4) ∨ (((p3 → True) → False) ∧ p3)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p2 ∨ ((p4 → p1) ∧ p1)) → (((p2 ∧ ((False ∨ p5) ∧ (True ∨ True))) ∨ p2) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h13
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255800107018534941171524562711 : ((True ∨ False) → (((True → (p4 → (((p1 ∧ p2) ∨ p2) ∧ False))) ∨ (((p5 ∧ ((p4 ∧ p5) → p4)) ∨ (p3 ∧ p2)) ∨ p1)) ∨ (p5 → True))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339115930719578448873174208431 : (p1 → (p1 ∧ ((((p4 → ((((False ∨ p5) → (False → True)) ∨ (((True ∧ p3) ∧ p4) → True)) ∨ False)) → (p4 → (p5 ∧ p5))) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46549689555641458475291839165 : ((((p2 ∧ True) → ((p1 → (True → (False ∧ ((False ∨ ((False → ((p4 → p2) ∧ p3)) → (p5 ∨ p2))) → p3)))) → p3)) ∧ (False → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149647706882224810892938549196 : ((p4 ∧ ((((p4 → (False → (p5 ∨ True))) ∧ p2) ∧ False) ∧ (((False ∨ p2) ∨ p3) ∧ ((False ∨ p3) ∧ False)))) ∨ ((False → p4) ∨ (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50253120597154819036148648584 : (((((p5 → p3) → (((True ∨ p5) ∨ (((((p4 ∨ p2) → p3) ∧ True) → p2) ∧ True)) → p2)) → p3) ∨ (True → (False → (p3 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198334859726542304547626093232 : ((p2 ∧ ((p2 ∨ ((p3 ∨ False) ∨ p5)) ∨ True)) ∨ ((((False ∧ True) ∧ (p1 ∧ p3)) ∨ ((p1 ∧ ((p5 ∧ p5) ∧ p5)) ∨ (True ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_444585541155735315058570213835 : ((((p1 ∨ ((p4 ∧ ((True ∨ (p2 ∧ True)) ∧ p3)) ∨ ((False ∨ ((p5 ∨ (p2 → p2)) → p3)) ∨ (p1 → p1)))) ∨ ((False → False) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147323857946205186251750344978 : (((((p1 ∨ (False ∨ ((((((p5 ∧ False) ∧ p4) ∧ True) ∨ False) → p2) ∨ p4))) → p5) ∧ (True ∧ p4)) ∨ False) ∨ (True ∨ ((p3 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179340276275295931900000773819 : ((p1 ∨ ((p5 ∨ p5) ∨ ((p4 ∧ ((p5 ∨ (p4 → p1)) ∨ p4)) ∧ p4))) ∨ (((True ∨ p1) ∨ p2) ∧ (p3 → (p4 → ((True ∨ p4) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637705114691143757166629394107 : ((((((p2 ∧ ((p3 → p5) → (p3 ∨ p5))) ∧ (False → p5)) → ((p1 ∨ ((p5 → ((p1 → p3) ∧ p1)) ∨ True)) ∨ (p1 → p1))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338141491512220975316657658879 : (p1 → ((p2 ∧ ((p1 ∨ (p3 ∧ (p4 → p2))) ∧ True)) ∨ ((((p2 ∨ (p3 → p3)) ∧ p4) ∨ p2) → ((p1 → p3) ∨ ((True → True) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299608332842855917879104203240 : (False ∨ ((((p5 ∨ (p4 ∨ (True ∧ p5))) → ((p3 → True) ∧ ((False ∨ (((p2 ∨ p3) → (p5 ∨ p4)) ∨ (True ∧ p2))) ∨ False))) → p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (p4 ∨ (True ∧ p5))) → ((p3 → True) ∧ ((False ∨ (((p2 ∨ p3) → (p5 ∨ p4)) ∨ (True ∧ p2))) ∨ False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49753038506529878631255969440 : (((p5 ∧ (p3 ∧ ((((p2 → False) ∨ ((p5 ∨ (p4 ∧ (False ∧ (p1 → False)))) → p5)) → p3) ∧ (p3 ∨ p2)))) → ((False ∨ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148856855996751565943743119720 : (((p3 ∧ (p4 ∧ (p2 ∧ p5))) ∧ (((True → (p5 → p3)) ∨ ((p2 → True) → ((p4 → p5) ∨ p3))) → p3)) ∨ (((False → p5) → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153832228277955144723814072557 : ((p5 → (p1 ∧ (((((False ∨ p5) → ((False ∧ (p1 ∧ (p4 ∧ p1))) → p5)) ∧ p5) ∧ (p5 → p4)) ∧ p2))) → (p2 → ((True → p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37188279075456040443627153683 : ((((((p4 ∨ False) ∨ (False ∧ ((p3 ∨ p3) → p4))) ∧ (p1 ∧ ((p2 ∨ (False ∧ ((p2 ∧ True) ∨ (False ∧ p5)))) → p2))) ∧ p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326325487970614045858432425126 : (p5 ∨ (p4 → (p2 ∨ (p2 → ((((False ∨ p1) ∨ (p1 ∧ p3)) ∨ (((p1 ∧ ((p1 ∨ True) ∨ (p1 ∨ p5))) → True) ∧ p2)) ∨ (p4 ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340827490392010214141116803318 : (p2 → (((p5 ∨ (((False ∧ p5) ∨ ((p1 → (p3 ∨ (p5 → False))) → (p4 ∧ (p2 ∧ ((p5 → False) ∧ p4))))) ∧ p4)) ∨ (False ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157211039990002125714121533264 : ((((p3 ∧ (p1 ∨ ((p3 ∧ True) ∨ ((p2 ∧ True) ∨ (True ∨ (p3 → p4)))))) → (p3 → True)) → p4) ∨ ((p2 ∨ p4) → (p5 ∨ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_191810531338243146669646638350 : ((p2 ∨ ((p1 ∨ p3) ∨ ((p4 ∧ (True ∨ p1)) ∨ p5))) ∨ (p3 → ((p3 ∨ (((((p1 ∨ p2) → (p2 ∨ False)) → False) → p2) → p5)) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133903620160351293770494326872 : (((p1 ∨ (p4 ∨ (((p1 → (p2 ∧ p3)) ∨ p4) ∨ ((p3 ∧ False) ∨ (p5 → ((True → (p1 ∧ True)) → False)))))) ∧ p4) ∨ (True → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230495697484839593870914648185 : (((True → p1) ∧ p2) → (True → (((((((False → p5) → (p3 → p5)) ∨ p1) ∨ True) → (False ∧ p2)) ∨ (True ∨ (True → (p3 ∨ p5)))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625124032554945696368187880715 : ((((True → (((((((p1 → p3) → (p4 ∧ (True → (True ∧ p1)))) ∧ (p2 ∨ p5)) ∨ True) ∧ p3) ∧ p4) → ((p1 ∧ p5) ∧ p5))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676200987433889467014067537354 : ((((((p2 → p2) ∨ False) ∧ ((p4 ∧ p1) ∧ (p3 ∧ ((p4 ∧ (p2 ∧ (p4 ∧ True))) ∨ (False → True))))) ∧ ((False ∨ p3) ∧ (p2 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117875763015807870822779891336 : ((p5 ∧ (((True ∨ (p4 → ((((p4 ∧ ((False ∨ (p1 → (p2 → p2))) → p3)) → True) → p4) ∧ (p1 ∨ p4)))) ∨ p5) → p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217364864183954819801930729823 : (((p3 ∨ (p3 → p5)) ∨ p2) → (((p2 ∨ p4) → p1) → (((True ∧ ((p2 → p4) ∧ ((p4 ∧ p5) ∧ p3))) ∧ p5) ∨ (True ∨ (p3 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_197220642188741024970058649811 : ((((p3 ∧ ((False ∨ p2) → p3)) ∨ p2) → p5) ∨ ((p3 ∧ (p1 → ((p4 ∧ (p1 ∧ p4)) ∨ p1))) ∨ ((p2 → True) ∨ (p3 → (p2 → p5))))) := by
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
theorem thm_5_vars_203824763268168528927129856141 : ((False → ((p1 ∧ (p1 → p2)) ∧ p2)) ∧ (p1 → (((p4 ∧ (p4 → ((p3 → (p2 ∧ (True → p2))) ∨ (p4 ∧ p1)))) ∧ (p4 ∨ p3)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147833881276158955728626285604 : (((p2 ∨ ((p1 → (((p2 ∧ ((p4 ∧ True) ∨ (p3 ∧ (False → p5)))) → (False ∧ p3)) → p4)) ∨ p4)) → p2) ∨ (((p2 → p5) ∧ p2) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66050980358832179693002838872 : ((p5 ∨ (((((((False ∧ p1) ∨ (True → (p3 ∨ p1))) ∧ (False → (p1 → True))) ∨ p1) ∨ (p2 ∨ (False → (False ∧ p1)))) ∨ False) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191764759739715238102589133109 : ((p1 ∨ ((p5 ∧ (True ∨ (p1 → (p3 → True)))) ∨ p1)) ∨ ((p3 ∨ (p4 ∧ ((p5 → (p2 ∨ True)) ∧ p3))) ∨ (((p1 ∧ p4) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300994332061675739918788043799 : (False ∨ ((((p1 ∨ (True ∨ p5)) → (p3 ∧ p1)) ∧ (p1 ∧ (p1 ∨ p3))) → ((((p2 ∨ p4) → (p5 → p2)) ∧ True) ∨ ((True ∧ p4) → True)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68197402501602115660502433486 : ((p3 → (((p2 → p5) ∧ (((p1 → ((p2 → p2) ∧ ((p3 → p4) → p5))) ∧ (p2 ∨ p5)) ∧ (p5 ∨ ((p1 ∨ p4) → False)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595357675284891720453728530362 : ((((((True ∨ p1) → (((p4 → True) → ((True ∧ p3) → p2)) ∨ True)) ∧ ((p3 ∨ p5) ∧ ((p5 → (p4 → p4)) → (p3 ∧ False)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313136595938757202475683340542 : (p3 ∨ (((p4 ∨ ((((p3 → p3) ∧ (p5 ∨ (p3 ∧ (True ∧ (p1 ∨ p1))))) → p3) ∧ p2)) ∧ ((p3 ∨ (p2 ∧ p1)) ∨ (p1 ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171639247328373349766313920887 : ((((p1 ∨ False) ∨ ((p2 ∨ True) ∧ (((p4 → p1) → (False ∧ p2)) ∨ True))) ∨ p2) ∨ ((((p3 ∧ p3) ∧ p1) ∧ ((False ∨ False) ∧ p4)) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674032729733092964102976608592 : ((((p1 ∧ (((((p3 ∧ p1) ∨ (p1 ∨ (p2 ∨ p4))) → p2) ∧ (((p4 → p1) ∨ (True → True)) ∧ p4)) ∨ p4)) → (False ∨ (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113826345576007529757472946843 : (((p5 ∧ (p5 → ((((((p5 → ((False ∧ (p5 → True)) ∧ p1)) → p3) → p4) → (p5 ∨ False)) → p3) → p1))) → (p1 → p2)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118380024649797215298517320242 : ((p2 ∨ ((((False ∨ ((((False ∧ False) → True) ∧ True) ∧ p1)) ∧ True) ∨ p1) ∨ (p1 → (p2 → (((False ∨ True) ∨ False) ∨ True))))) ∨ (p4 ∧ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177781658463417035804946905162 : (((p4 ∧ ((p2 → ((p5 ∧ p5) ∧ ((p1 ∧ p2) ∧ p3))) ∧ False)) ∧ p1) ∨ ((p4 ∧ (((p3 ∨ p2) → True) ∨ p3)) → (p3 → (p5 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47263620230993418341447017850 : ((((p1 ∨ (((p4 ∨ p5) ∧ p2) → False)) → ((p2 ∨ (((p3 ∧ True) ∧ p4) → (p2 ∧ False))) ∨ (False ∨ (False ∧ p5)))) ∨ (True ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55836817281780835750602472642 : (((False ∧ (p4 ∧ (p3 → p4))) ∧ ((p4 ∧ p3) ∧ (((((p1 ∨ p4) ∧ p4) ∨ ((p1 → (False ∧ p1)) ∧ (p3 ∧ p3))) → p4) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174103207474035191802712861354 : ((((p3 ∨ p1) ∧ (p5 ∨ ((p5 → ((True ∧ p5) ∨ False)) → p4))) ∧ (p1 → True)) → ((((p2 → (p4 ∧ False)) ∧ (p5 ∧ p5)) ∧ p2) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2668290741818146066141923389 : ((p3 ∧ (((p4 ∨ p1) ∧ p2) ∧ p2)) ∨ ((((p1 ∨ (((p5 → p1) ∧ True) ∨ p1)) → (p3 ∧ True)) → p4) → ((p4 ∧ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741494959267097082317215171366 : ((((p5 ∨ p3) ∨ ((((((p5 → p4) ∧ p3) ∧ p5) ∨ ((((p5 ∨ p2) ∧ (p1 ∧ True)) ∨ p3) → ((p3 → p1) ∨ p4))) → p4) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179493297095146659115053878193 : ((True → (p4 ∨ (p4 ∧ (False ∨ (True → ((False ∧ p4) ∨ (p4 ∧ False))))))) ∨ (((p2 ∧ p5) ∨ p4) ∨ (p2 ∨ (False ∨ (p1 → (True ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681582298048722195144062123822 : ((((p1 → ((((True → ((p3 ∨ p1) ∨ p4)) ∧ p5) → p1) ∨ ((p2 ∨ p1) ∧ ((p3 ∨ p3) → p2)))) → ((p3 → p3) ∧ (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349415151810864953134518077669 : (p3 → (p4 → ((p4 ∧ (((p1 ∧ p2) ∨ ((p1 ∧ (p4 ∨ (False → False))) ∨ (p1 → False))) ∧ p3)) ∨ ((p5 ∧ (p4 ∨ p3)) ∨ (p4 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317287168746387314166332698953 : (p4 ∨ (((p5 ∨ ((((False ∨ ((p4 ∧ (p4 ∧ (p3 ∧ p3))) ∧ p2)) ∨ (True ∨ ((p4 ∧ p1) → p4))) → p1) → p1)) ∨ (p5 ∨ p3)) ∧ True)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ ((p4 ∧ (p4 ∧ (p3 ∧ p3))) ∧ p2)) ∨ (True ∨ ((p4 ∧ p1) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690025113256898184321929044455 : ((((p3 ∧ ((((p2 ∧ p5) ∧ ((p2 ∨ True) ∨ p5)) ∧ (False → (False → True))) → p3)) ∨ ((p2 ∨ (True → (True ∨ (p1 ∨ False)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328469327656109614410827784001 : (True → ((p2 ∨ (p3 ∨ (p3 ∨ ((p5 ∧ ((p4 → p4) ∨ ((p3 → (True → True)) ∨ False))) ∧ p4)))) → (((p3 → (False ∧ p1)) ∧ p5) ∨ True))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197667103320068804404471390831 : ((((False ∧ p5) → (True ∧ p4)) → (p4 → p1)) ∨ ((False → (True → ((p3 ∧ (True → False)) → p1))) ∨ (p1 → ((False ∧ p1) ∨ (p3 → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193863522119080341755892195230 : ((True ∨ (p3 ∨ (p4 ∨ ((p3 ∨ False) → (False ∧ p3))))) → (True → ((((p4 ∧ ((p2 ∧ p4) ∧ (p5 ∧ p3))) ∧ True) ∨ p4) ∨ (p1 → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196339052396590903998531514427 : ((p4 ∨ (p2 ∨ ((p2 ∧ (p1 → False)) ∨ True))) ∧ ((p3 ∧ ((p3 ∧ ((p2 ∧ p5) ∧ p2)) ∧ p2)) ∨ (((False ∧ (p5 ∧ p5)) ∧ p5) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156857432829952085114368794983 : (((((p2 ∧ ((True → (p4 ∧ (p5 ∨ ((p1 ∧ False) ∨ p5)))) ∨ (p3 ∧ p5))) ∨ p5) ∧ False) ∨ p3) ∨ ((False ∧ p2) → ((p4 ∧ True) ∨ p1))) := by
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
theorem thm_5_vars_737797712619880603046469916341 : ((((True ∧ False) ∨ ((p5 → ((p2 ∧ (((False → True) ∨ p2) ∨ True)) → ((((True ∧ (p5 ∧ False)) → False) → p3) ∨ (p5 → p1)))) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_213148965544997087253970650041 : ((((False ∧ True) ∨ p5) ∧ p4) ∨ ((((p4 ∨ True) → (((p4 → (p5 ∨ (p4 ∨ ((p5 ∨ p4) ∧ p4)))) ∧ p5) → False)) ∨ (False → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309329183296925075245782153501 : (p2 ∨ ((((((p3 → (p1 ∧ (False → p5))) → (p1 → (((False ∧ p5) ∧ p2) ∧ (p1 → p4)))) ∧ p5) → p4) ∧ (True ∧ False)) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125691083586866039600787831493 : (((True ∨ p2) ∨ (p3 → (p4 ∧ ((p5 ∨ (((False → ((p1 → p2) → p4)) ∧ (p5 → True)) → p3)) → ((p2 ∨ p1) ∧ False))))) → (p4 ∨ True)) := by
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
theorem thm_5_vars_342162221558935963274852918985 : (p2 → ((((False ∨ ((p3 ∨ p1) ∨ True)) ∧ p2) ∧ ((p1 → p4) ∨ ((p3 ∧ False) ∨ ((p4 → p3) ∧ p5)))) ∨ (((p3 ∨ True) ∨ p4) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710660765610127901358706956067 : ((((((p4 ∨ p2) → p3) ∨ (p5 → p3)) ∧ ((p1 ∧ p4) ∧ ((p4 ∨ True) ∧ ((((((p2 → p5) ∧ p2) ∧ p5) → False) ∧ p1) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354502186852972071268459764856 : (p5 → ((p3 ∨ ((((p3 → (p1 → p3)) ∨ (((False → p1) ∧ ((True ∨ p3) ∨ (p5 ∨ False))) ∧ p3)) → (p2 ∧ (p1 ∧ p3))) ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_135093419622998303376537405953 : (((((((False ∨ p5) → p5) → False) ∨ (False ∧ False)) ∧ ((((True ∨ p4) ∨ (p4 → False)) ∧ False) → p5)) ∨ (p3 ∧ p2)) ∨ (p1 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1965082318153478141232232917 : ((((p2 → p1) ∧ True) → (((p1 ∨ (True → (p3 → False))) ∧ (False ∧ p3)) ∧ (p3 ∧ (p1 → p4)))) ∨ (False → (p5 ∨ (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244454678640690389014866407153 : ((False ∧ p2) ∨ ((True ∨ ((p3 ∨ (p4 ∧ True)) ∨ ((p5 ∧ (p4 ∨ False)) → p3))) → ((p4 ∨ ((p1 ∨ p1) ∨ ((p4 → p1) ∧ False))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
theorem thm_5_vars_729027461810121808858264894867 : (((((p3 ∨ p4) ∧ p2) → ((((((((p3 → False) → (p2 ∧ (p1 → p4))) ∨ p4) ∧ p2) ∧ p2) ∨ p2) ∧ (p5 ∨ (False ∨ True))) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258216413180557588705130719698 : ((p4 ∨ p5) → (((((((((p3 → True) ∧ p4) → (p2 ∧ (p4 → p3))) → p1) ∨ p4) → p2) → (p2 ∧ (p4 → (p5 ∨ p2)))) ∨ False) ∨ True)) := by
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
theorem thm_5_vars_43581013413304071109848078419 : ((((((p5 ∧ (False ∨ ((((p2 → (p5 ∧ (p4 → p4))) ∧ p1) ∨ (p1 ∨ p5)) → ((False → p4) ∧ p2)))) → p2) ∨ True) → p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655541626049792443137070233010 : (((((((((True ∨ p4) ∨ True) ∨ p1) ∨ ((((False → p1) ∧ True) → p5) → (True ∨ p2))) → (p1 ∨ p1)) → (p1 → p4)) ∨ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160545070548170896742022440005 : (((False ∨ (((p4 ∧ False) → (True → (True ∨ False))) ∨ (p3 ∧ p4))) ∨ (((p3 ∧ p3) → p4) → p5)) → (p4 → ((False ∧ (False ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179322778043100893379455644271 : ((p1 ∨ (((p2 ∧ (False → (False → p1))) → ((p1 ∨ True) ∧ p3)) ∧ True)) ∨ (p1 → (((((p1 ∨ (True ∨ False)) ∧ p1) → p3) → p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308484798886457939014080914452 : (p2 ∨ (((((((((p2 → False) ∨ p2) → ((False → p1) ∧ p2)) → p3) ∨ (True ∧ p2)) → (p1 ∧ p5)) ∧ False) ∨ (p4 ∨ (p2 ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662170266738758869522623482780 : (((((p1 → ((((p4 → False) → p4) ∨ p2) ∧ ((True ∧ p2) ∨ p3))) → ((((p4 → p1) → p3) → (p2 → True)) → False)) → (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598900714833082990792163365288 : (((((True ∨ p2) ∧ (((p4 ∧ ((((p5 → p5) ∧ False) ∨ (p2 ∨ (p5 ∨ False))) ∨ (p4 ∨ (p5 ∧ (True ∨ True))))) → p5) → False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306451994092174602403642465630 : (p1 ∨ ((p2 ∨ p5) ∨ (((True ∨ (((p1 ∨ p1) ∧ p5) ∧ (((p1 → False) ∧ False) → True))) ∧ (p5 ∨ p5)) ∨ (p1 → (p5 ∨ (p4 → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300667893780449761750817821808 : (False ∨ (((p3 ∧ ((p4 ∧ (True → p1)) → ((p3 ∧ (p5 → (True ∧ p3))) ∨ (p5 → True)))) ∨ p4) ∨ (False → (p2 ∧ ((p3 → p2) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44776141305429284546276452097 : ((((True ∨ ((p4 ∧ p4) ∨ p2)) → (((p4 → (p4 ∧ p5)) ∧ (False ∨ (((p4 ∧ p5) ∧ (p2 → (p1 ∧ p5))) ∧ True))) → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44793398135335811680223442133 : (((((p4 ∧ False) ∨ p3) ∧ ((p1 ∨ (p1 → (True ∧ ((((True ∨ p2) ∧ p5) ∨ (False ∧ p3)) → (p1 → (p5 ∧ p2)))))) ∨ False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115294422977588682259743412006 : ((((((True ∧ (False → p2)) ∧ p1) ∧ (True ∧ p2)) ∨ p2) → (False ∨ (p4 ∨ ((p4 ∨ ((True ∧ False) → p2)) ∧ (p3 ∧ False))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113472731949138817485033668557 : (((((((p3 ∨ ((True ∨ (False ∨ p1)) ∧ (p4 ∨ p5))) → p1) ∧ ((p5 ∨ p5) ∨ p3)) ∧ p5) ∧ (False ∨ p2)) ∨ (p3 ∧ p2)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231365876314412310061987142844 : (((False → p2) ∨ p1) → (((True ∨ p2) → ((p5 ∧ ((((False ∧ p4) → p4) ∧ ((False → (p5 → p1)) ∨ p5)) ∧ p3)) ∨ (True → True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112414426125259835645925967775 : ((((p1 ∨ ((p4 ∧ p3) ∨ (p1 → ((p2 ∨ False) ∧ ((((p2 ∧ p3) ∧ ((p1 ∧ p5) ∨ p3)) ∧ p1) ∨ p2))))) ∧ p3) → p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137030279780471900198651345276 : (((p4 ∨ p5) → (((p5 → (p4 → p3)) ∧ ((p3 → (True ∨ p1)) → ((p1 → ((True ∧ True) ∨ p2)) ∨ p3))) ∨ p5)) ∨ ((True ∧ False) → p2)) := by
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
theorem thm_5_vars_54497790424996051000638237926 : ((((p1 ∧ (False ∧ p3)) ∧ (p3 ∧ (p3 ∨ p2))) ∨ (((False → (((p4 ∧ p4) ∧ ((False → p5) ∧ p2)) ∧ (False → p5))) ∨ p3) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619354358579459382656309114239 : ((((((True ∨ p3) → p5) → (p3 ∧ ((((True ∧ False) ∨ p1) ∨ ((((p3 ∧ False) → (p1 ∧ p5)) → p3) ∨ (p4 ∨ p2))) ∨ p5))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159042146535049886209748658370 : ((p5 ∨ (((p5 ∨ p2) → (((p1 → p5) ∧ ((p5 ∨ p2) ∧ (p5 → True))) ∧ (p2 ∨ p3))) ∧ p1)) ∨ (True ∨ ((p2 ∨ (True ∨ p5)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2792939862317963273439341782 : ((False ∧ (p3 → (p4 ∧ True))) ∨ (((p3 ∧ p1) ∨ (((True → ((p3 ∧ p5) → p4)) ∧ p3) → p2)) → (((False → p5) → p5) → p5))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187453996751248837433186356821 : ((True ∨ ((((p1 ∧ True) ∨ (p4 ∧ True)) ∧ p5) ∨ (p3 ∧ p5))) → ((p4 ∧ (False → p5)) ∨ (((p1 ∨ p1) ∨ p1) → (p5 ∨ (False → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
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
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h24
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h34 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230008983198832427083432150823 : (((p1 ∧ True) ∧ True) → (((p4 ∧ ((((p1 ∨ (True ∧ (p3 → ((p4 ∨ p3) ∨ (p4 → p1))))) ∧ p1) → p2) ∧ (p5 ∧ p4))) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8



