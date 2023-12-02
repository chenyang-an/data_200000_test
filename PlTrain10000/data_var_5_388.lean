variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180751584067185772376871650062 : (((p1 ∧ (p5 → (p1 ∧ p5))) ∨ (True → (True → ((False → p4) → False)))) → (((p3 ∨ ((False → (p2 → p3)) → p1)) ∧ (False → p3)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h18 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h25 := h22 h23
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308566723767256561189301132824 : (p2 ∨ ((((p2 ∨ ((p2 ∨ p4) ∨ p3)) → p3) → ((p3 ∨ (p5 → (((False → (p2 → False)) → False) ∨ (True ∨ p2)))) ∨ (p4 → False))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156892580660647565169118766855 : ((((((False ∧ p5) ∧ p1) ∧ (((p1 ∨ ((p5 ∨ p5) → (True ∧ False))) → True) ∧ p5)) ∨ p3) ∨ p5) ∨ ((p1 → p3) → (True ∨ (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40030772918532642509050083814 : (((((((p4 ∨ p3) ∧ ((((p3 ∧ (((p1 ∨ p4) → (True → p4)) ∧ True)) → p2) → p5) ∧ True)) → (p5 → False)) ∧ False) ∧ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39154428016741099239840621546 : ((((p1 ∨ p5) → (((((True ∧ True) ∨ p1) ∧ p1) ∧ p5) → ((True ∧ ((p5 ∧ (((p4 ∧ p1) → p3) → p3)) ∧ True)) → p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207302882151232858233699435156 : ((((p2 → (False ∨ p3)) → p4) ∨ p2) → ((False ∧ ((False ∧ p5) → (p5 ∧ (p5 ∨ False)))) ∨ (p5 ∨ (p4 ∨ ((p3 ∧ (False ∧ p1)) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62801767441773342795773127867 : ((p4 ∧ ((True ∧ (((False ∨ (False ∨ (p2 ∨ ((False ∨ False) ∨ p5)))) → False) ∨ p3)) ∧ ((((p1 ∧ p5) ∧ p3) ∧ (True ∧ p3)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787335201363386932001019664614 : (((p4 ∨ (p2 ∧ (p5 ∨ ((p3 ∧ p5) ∧ ((True ∧ ((False ∧ p3) ∨ (p3 ∨ ((p3 ∨ (p1 → p1)) ∧ False)))) ∨ (p1 ∧ (p2 → p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695196449509268076721897813498 : (((((False ∨ (((True → p4) → p1) ∨ (((True ∨ p2) ∨ p4) ∨ False))) ∨ True) → ((True ∧ (p5 ∧ ((p4 ∧ (p4 ∧ p1)) → p3))) ∨ True)) ∨ p3) ∧ True) := by
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
      -- False on the left can always be used.
      apply False.elim h3
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
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Disjunctions on the left can always be decomposed.
            cases h8
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
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205613666017816897866228321799 : (((False ∧ False) ∨ (p5 ∧ (p4 ∧ False))) ∨ (p3 ∨ ((False ∨ ((((p4 ∧ (p5 → (p3 → False))) ∨ p5) ∧ p5) ∧ (p5 → p4))) ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116865828759302831367422229081 : (((p1 → p4) ∨ (p2 ∧ (((True ∨ (p2 ∨ ((p5 ∧ p3) ∨ (((p4 ∨ (False → p3)) ∨ False) ∧ (p2 ∧ p3))))) → False) ∨ p5))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792650826687043197815327440215 : (((True → ((p2 → (True → ((p1 ∨ p5) ∧ p4))) ∨ ((p3 ∧ ((p5 → ((True ∨ True) ∧ ((False ∨ p5) ∨ False))) ∨ p2)) ∨ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397320298879069826256451418516 : ((((p1 ∨ (p2 ∧ (((p3 ∧ p5) ∨ ((True → (True ∧ ((p5 ∨ (p1 ∧ p2)) ∧ (p3 → (p5 ∨ p2))))) ∨ False)) ∧ (True ∧ p3)))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_160420774726942815631744550370 : (((((p2 → p4) ∧ p4) ∨ ((p3 → p5) → (p4 ∧ (p3 → (p1 ∧ p3))))) ∨ ((False → False) ∨ p3)) → (p5 ∨ (False ∨ (False → (False ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68432818566000476559577645347 : ((p3 → ((p1 ∨ p1) → ((((((False ∨ False) ∧ p1) → False) → ((p2 ∨ (p2 ∨ p3)) → (p2 → (p4 ∨ (p5 → p2))))) ∨ p2) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181200758608459443472196394987 : ((p2 ∧ ((((p2 ∨ (False ∧ False)) → (p4 → p1)) → (False ∧ p3)) → p2)) → ((((p4 → True) ∧ (True ∨ ((p4 ∨ True) → p1))) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 → True) ∧ (True ∨ ((p4 ∨ True) → p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112487158772372293705754203619 : ((((p4 ∧ ((p1 ∧ (((False → (True ∧ (False ∨ p2))) → (True → p2)) → (p1 ∨ p3))) → ((False ∨ p1) ∧ False))) ∨ True) → p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178488055022447017622494153356 : (((((p3 → False) → False) ∨ (False ∧ (p1 ∧ p5))) ∨ ((p1 ∨ False) ∧ False)) ∨ ((((((p1 → (p1 → True)) ∨ True) ∨ True) ∨ p5) ∨ p3) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244750686538932361240277236334 : ((p1 ∧ False) ∨ (((p2 ∨ ((True ∧ ((p3 ∨ (((p1 ∨ p5) ∧ False) ∨ p1)) ∨ False)) ∧ ((p4 ∨ p4) → p2))) ∨ True) ∨ ((p2 ∨ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60092899374345162514202097108 : (((p3 ∨ False) → ((True ∧ ((False ∧ False) ∧ (((((p3 ∧ True) ∨ (p1 ∧ True)) ∧ ((p1 → False) ∧ p2)) ∧ (p5 ∧ p2)) ∧ p1))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596180500000731961277118270758 : (((((((((p4 → False) ∧ p3) → p4) → True) → p1) ∧ (p5 → ((False ∨ (p1 ∨ True)) ∨ ((((p3 → p2) ∨ False) ∧ False) ∨ p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38468224858953663508930104693 : ((((p4 ∨ (p1 → ((p4 ∧ p5) ∨ (p1 → ((False → (p1 ∨ p5)) ∧ p3))))) → (((p5 ∧ (True ∧ p4)) ∨ (p5 ∨ p2)) → p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115290586958692055733001801188 : ((((p5 ∧ (((p1 ∧ (p4 ∨ True)) ∧ True) ∧ p2)) ∧ p1) → (((((p5 ∨ p3) → True) → p5) ∨ (p5 ∨ False)) → (p3 ∧ True))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357462518720155686345930498992 : (p5 → ((p2 → p4) → (p3 ∨ ((((((p1 ∧ (p1 ∨ p4)) → ((p5 ∧ False) ∨ False)) ∧ p1) ∨ (((True ∧ True) → False) ∧ p2)) ∨ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134518911662334888948938435794 : ((((True → (((p1 → p3) → ((p4 ∧ p2) → (p3 → ((p3 → (p4 ∨ (p2 → p3))) ∧ True)))) ∨ p4)) ∨ p5) → p4) ∨ (p4 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116406579862643425275630012520 : (((True ∨ (False ∨ False)) → ((p4 → ((p2 → False) → (((p1 ∧ True) ∨ ((p1 → p5) → (p2 ∨ (p1 ∨ p3)))) → p1))) → p3)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53751620437275943420659959370 : ((((((False ∧ p5) ∨ (p1 ∧ p5)) ∧ (p4 ∧ True)) ∧ p1) ∨ (((p3 → p1) → (p5 ∧ (p4 → p4))) → (p4 ∨ (False → (False ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179873619011628030789022754296 : (((p4 → (p1 ∨ (p1 → (((p5 ∨ False) ∧ (p4 ∧ p2)) → p4)))) ∧ p5) → (p2 → ((((p4 ∨ p2) → (p3 ∨ False)) ∨ True) ∨ (p1 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46473307420616842095483870255 : ((((p4 ∧ (p2 ∧ True)) ∧ (True → ((False → p2) → (p4 ∧ (((p2 ∨ p2) ∨ (((p1 ∨ p5) ∧ p5) ∨ p5)) ∧ p3))))) ∧ (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62176204827524064818080894277 : ((p2 ∧ (p5 → (((False → True) ∨ (((p1 ∧ True) ∧ (((p4 ∨ p3) → p1) ∧ ((p2 ∨ p4) ∧ (p1 → (False ∧ True))))) ∧ p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745527236256383253989244010740 : ((((True ∨ False) → (((p4 → ((p5 → True) → p2)) → p3) → ((p1 ∨ False) ∧ ((p5 ∨ (False → True)) → (((p2 ∧ p1) → False) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321279303268381111359400661778 : (p4 ∨ (p4 ∨ (p5 ∨ ((p3 → ((((p3 ∧ (p4 → True)) → p4) → (p1 ∨ ((False ∨ p4) → (False ∨ p1)))) → p5)) → (p5 ∨ (p3 ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42358935230412062803692977627 : (((p3 ∧ (p3 ∧ (((p1 ∨ ((p3 ∧ False) ∧ (False → ((True ∨ (p3 → p1)) ∧ p3)))) ∧ False) ∧ (p3 → (p3 ∧ (False ∧ p1)))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257477569657962084253467265026 : ((p3 ∨ True) → (p1 → ((((p1 → p5) → (p5 ∨ (p2 ∨ ((p5 ∧ p3) → (p1 ∨ p5))))) → ((p2 → p4) → p3)) ∨ ((p5 ∨ False) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66815876345943536298956097545 : ((True → (p5 ∨ (p1 ∧ (p2 ∧ (((p3 ∨ ((p4 ∧ ((p4 ∨ p3) ∨ (True ∨ (p3 → p5)))) ∨ (p3 → p1))) → (p2 ∧ p3)) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159184305507587700089740593784 : ((p1 → (p3 ∨ (((p4 ∧ p1) → False) → ((((p3 ∨ p5) ∨ (p2 ∧ p5)) ∨ p1) ∧ (p4 → p1))))) ∨ ((p1 ∨ (p5 → p4)) ∧ (p4 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219435403268474481824336951463 : ((p4 ∨ ((p1 → True) ∨ p5)) → ((False → ((p4 ∧ True) → True)) → ((((False ∨ True) → False) ∨ ((False → (True → (p1 ∨ False))) → True)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314567670878475649718069178019 : (p3 ∨ ((p5 → (((p2 → (((True → p2) → True) ∧ p5)) → (p4 ∨ (p5 → p2))) ∧ (p3 ∨ p1))) ∨ (((True ∧ p3) → p2) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41205274488604019486345905973 : ((((p4 ∨ (((p5 ∨ ((((p2 ∧ (p3 ∧ (p3 → (p1 ∧ True)))) ∨ p3) → p1) → p4)) → p5) ∨ p4)) → (p3 ∨ (False ∧ p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730777333401688133786665659499 : ((((p4 ∧ (p4 ∨ p4)) → ((p3 ∨ ((p3 → (False ∨ (((p2 → p3) → (((p4 → p3) → False) → p5)) ∨ p2))) ∨ p3)) ∨ (p1 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158165054099209288967805002130 : (((((p3 ∨ True) ∨ p1) ∨ p4) → (p4 ∨ (((True → (p5 ∨ p4)) → p3) ∨ ((p2 ∨ p3) ∧ False)))) ∨ ((((p5 ∨ p1) ∨ False) ∧ False) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658514513332109533997118121817 : ((((p2 ∨ ((((True ∨ p2) ∨ (((((True ∨ p5) ∧ (p2 ∨ False)) ∧ p5) → (True ∧ p1)) → (p4 → p2))) ∧ p1) → p4)) ∨ (False → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_190175815755426102027464437255 : (((p4 ∧ (((p4 → False) ∨ (p5 ∧ p2)) ∨ p5)) ∧ False) ∨ (((p1 ∧ p5) ∨ p3) → (((p5 ∧ False) ∧ (p3 → (p4 ∧ (p1 ∧ p3)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245890132758062882861423591877 : ((p3 ∧ p5) ∨ (((p5 ∧ ((p2 → p4) → (((False ∨ p3) ∨ p3) → (True ∧ (p4 ∧ p5))))) → (((p3 ∨ True) ∨ (False ∧ False)) → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798619472580161441810666557002 : (((p1 → (((p5 ∨ p1) → (False ∧ (p3 → p1))) → (((((p4 ∧ (p2 ∧ p5)) → True) ∨ p5) → ((False ∨ (False ∧ p1)) ∨ p2)) ∨ p1))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69022820223937602779024896971 : ((p5 → ((((p4 ∧ ((((p1 → True) ∧ p2) → (p1 ∧ p1)) → ((True ∧ ((p5 ∧ p1) → True)) ∨ True))) → (p1 ∨ p5)) ∧ False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617621964043278868625811445887 : ((((((((p4 → p2) ∧ p2) → p5) ∧ p2) ∨ ((((p1 ∧ p2) → p3) ∨ (p1 ∧ (p2 ∨ ((p5 ∧ False) ∧ (True ∧ p3))))) ∨ True)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316960925437240304591299539922 : (p3 ∨ (p2 → (True → ((p4 ∧ p5) ∨ (p3 ∨ ((p5 ∨ (p3 → ((True → p5) ∨ (((p3 → p1) → p4) → (p1 → p5))))) ∨ (p3 → p2))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46247569372828034733032647556 : ((((p3 → (p1 ∧ ((((p1 → (((p4 → p2) ∨ p4) → (p2 → p2))) ∧ p1) ∧ p5) ∨ (False ∨ p2)))) ∨ (p5 ∨ False)) ∧ (True ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188116127538393488135339199905 : ((((((p1 ∨ (p4 ∧ p1)) ∧ p1) ∧ False) ∨ p1) ∨ True) ∧ (((((((True → (p3 → False)) ∧ p3) ∧ p4) ∧ False) ∧ p4) ∨ (p5 ∧ False)) → True)) := by
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
theorem thm_5_vars_774351773329911822690785376250 : (((False ∨ (((p3 ∧ (p1 ∧ ((p2 ∨ False) → (p5 ∧ (p2 ∧ (p3 ∨ (p4 ∧ (False ∨ True)))))))) ∧ True) ∨ ((p3 ∨ p5) → (False → p4)))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65085215169408210248045925960 : ((p2 ∨ (False ∨ (((p3 ∨ (p1 ∨ ((p1 ∧ p5) → (p2 ∧ (p3 ∨ p2))))) ∧ (p3 ∧ (p2 ∧ (p5 ∧ p2)))) ∨ (p3 ∧ (p2 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225248517684212310707137921531 : (((True ∨ True) ∧ p1) ∨ (p5 ∨ ((p4 ∨ (((p2 ∨ p4) ∧ p3) ∨ (p3 → (((p5 → p5) ∨ p3) ∨ False)))) ∨ (p2 ∧ (p5 ∧ (True ∧ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353834969028616160826441990214 : (p4 → (p1 → (((p5 ∧ ((p1 → ((((True → ((True → (p1 → p4)) → (False ∨ p5))) ∧ (p4 ∧ True)) ∧ p3) → True)) → p5)) ∧ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709079164234245562887623744768 : ((((((p1 ∧ p4) → False) ∨ ((p3 ∧ p3) ∨ p3)) → (False ∨ (((p5 ∧ p5) ∨ (p2 ∧ ((True ∨ (p1 ∨ (False ∨ p1))) ∧ p5))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600630935180133761446209080106 : ((((False ∧ ((((p2 ∨ (((p4 → (True ∨ p3)) ∨ (((p1 ∧ p2) ∨ True) ∨ (False → p4))) ∧ (False → p3))) → p4) ∧ False) ∨ p1)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41728958022206523355471172877 : (((((p5 ∨ p5) ∧ (p4 ∧ p5)) ∧ (((((((p2 → p2) → p1) → ((p3 ∨ False) → p3)) ∨ p3) → (p3 → p3)) ∧ p5) ∧ False)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44640526282014570645423337617 : (((((((False ∧ p1) → p3) ∧ p2) ∧ p4) ∨ ((True ∧ p5) → (((((p1 ∧ (True → True)) → p4) → False) ∧ True) ∧ (False ∧ p3)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336314810724058276313465138942 : (p1 → (((p2 ∧ ((p5 ∨ p5) ∨ p5)) ∨ (p5 ∧ ((p5 ∨ (p2 ∨ (((p3 ∧ (p1 ∧ (p5 → False))) ∨ True) → p1))) ∧ (p5 → p2)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750877235507414535737441824264 : (((True ∧ (((((p5 → True) → (True → p5)) ∨ True) ∨ p2) ∧ (((((p1 ∧ p4) → (p1 ∨ ((p2 ∧ p2) ∧ False))) → p4) ∧ True) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309804791228989886368845743849 : (p2 ∨ ((((p1 ∧ False) ∧ p2) ∨ ((True → ((p4 ∧ p5) ∧ False)) → ((p1 ∨ ((p1 ∨ p1) → False)) → p5))) ∨ ((False → (False ∧ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324089995273129764431538534899 : (p5 ∨ ((p2 ∧ (p2 ∧ (p3 ∨ ((p4 ∧ p2) → (p2 ∧ (False → True)))))) ∨ ((((p2 ∧ False) ∧ (p5 ∧ True)) ∨ ((False → p3) ∧ True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149539729686984844425881877956 : ((p2 ∧ ((False ∨ (((((p5 ∨ p4) → p5) ∧ p1) ∨ (False ∨ p5)) ∨ ((p2 → (p2 ∨ p2)) ∧ p4))) ∨ p3)) ∨ ((p4 → True) ∨ (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206448552198002814617332448887 : ((p4 ∨ ((p2 ∨ p4) ∧ (p4 → p2))) ∨ ((False ∧ (p4 ∨ p1)) ∨ ((p1 → (p4 → True)) → (((p5 ∧ p1) ∨ False) → (p5 ∨ (p1 ∨ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118556434910222933971294272708 : ((p3 ∨ (p3 → ((((p5 → (p4 ∧ True)) ∨ (True → False)) ∨ p3) → ((((p3 ∧ p1) ∧ p2) → (p3 ∧ (p4 ∧ p2))) → p5)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748048689671587596903431695651 : ((((p1 → p1) → (((p3 → p2) ∨ p5) ∨ (True ∧ ((p3 ∨ True) ∧ (p3 ∨ ((True ∧ p3) → ((False ∨ ((True → False) → p1)) ∨ p5))))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707503317704743804765731369208 : (((((p5 ∧ (False ∧ p3)) ∨ (p5 ∨ (p1 ∧ False))) ∨ ((p3 ∨ ((p5 ∨ p4) ∨ ((p4 ∧ (((p1 ∧ True) → True) → p2)) → p4))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134335098940312899056220654645 : (((p3 ∧ (p1 ∨ (((((p2 ∧ (p1 ∨ False)) → p3) ∧ ((True → True) → p1)) ∧ p5) ∧ ((p3 ∨ p1) ∨ p2)))) ∨ p1) ∨ (p4 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161427176015385331059042678896 : ((p2 ∧ (((p1 ∨ (p4 → (p4 ∨ (False ∧ ((p3 ∧ p2) → p2))))) ∨ p4) ∧ (True ∧ (p2 ∨ p4)))) → (p4 ∨ (((p1 ∧ p4) ∨ p2) ∧ True))) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_516090800264190185662013438612 : ((((p2 → p3) ∨ ((p4 ∧ p3) → (p1 ∨ ((((p1 ∨ (p4 → (p2 ∧ p2))) → p4) → p5) ∨ (p5 ∨ (((p3 → p5) ∧ p3) → p5)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778895856024289653413123522743 : (((p1 ∨ (p1 → (((p5 ∧ p5) ∨ ((p1 ∧ True) ∨ ((True ∨ p2) → ((p3 ∧ True) ∧ ((p1 ∧ p2) ∨ (p1 ∨ False)))))) ∧ (p4 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161507768805580735756105721602 : ((p4 ∧ ((p1 → (((p3 ∨ p1) ∨ p5) ∨ p5)) → ((p5 → ((p5 → (p4 ∨ False)) ∧ True)) ∧ p5))) → (p4 ∧ (p3 → (True ∧ (p3 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p1 → (((p3 ∨ p1) ∨ p5) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114930018771466780818444277961 : ((((((p2 ∧ ((p5 → False) ∨ True)) ∨ p5) ∨ p4) ∧ ((True ∨ True) → False)) → ((p2 ∧ p4) ∨ (False ∧ ((False ∨ p3) ∨ p3)))) ∨ (p2 → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : (True ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h10 := h3 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h12 : (True ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349469060216620150953210882502 : (p3 → (p5 → ((((p2 → False) ∧ (p4 ∨ (((p4 ∨ True) ∨ p3) ∧ (p3 ∧ (p3 ∨ (p2 ∨ ((False ∧ p1) ∨ p3))))))) ∨ p5) → (p1 ∨ p5)))) := by
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h10.left
          let h14 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h18 =>
              -- Disjunctions on the left can always be decomposed.
              cases h18
              case inl h19 =>
                -- Conjunctions on the left can always be decomposed.
                let h20 := h19.left
                let h21 := h19.right
                -- False on the left can always be used.
                apply False.elim h20
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h10.left
          let h25 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h27 =>
            -- Disjunctions on the left can always be decomposed.
            cases h27
            case inl h28 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h29 =>
              -- Disjunctions on the left can always be decomposed.
              cases h29
              case inl h30 =>
                -- Conjunctions on the left can always be decomposed.
                let h31 := h30.left
                let h32 := h30.right
                -- False on the left can always be used.
                apply False.elim h31
              case inr h33 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h10.left
        let h36 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h41 =>
              -- Conjunctions on the left can always be decomposed.
              let h42 := h41.left
              let h43 := h41.right
              -- False on the left can always be used.
              apply False.elim h42
            case inr h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
  case inr h45 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748249156952144522661317826684 : ((((p2 → True) → ((p3 ∨ p4) → ((((True → (True ∧ (p1 → p1))) ∧ (((p2 → p3) → (p3 ∨ False)) ∧ p3)) ∧ p3) ∨ (p2 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177854138813561253863963849503 : (((((False ∧ (p1 ∧ (True ∧ ((False → p1) ∨ p2)))) ∨ p4) ∨ p3) ∨ p1) ∨ ((True ∨ ((p2 → (((p3 → p2) ∨ False) → True)) ∧ p4)) ∧ True)) := by
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
theorem thm_5_vars_165640804719240471181283460063 : (((p3 ∨ (((p2 ∧ p2) ∨ False) ∨ p3)) ∧ ((p5 → (p4 → p2)) ∧ (p3 ∨ (p1 ∨ True)))) ∨ ((p4 → (p5 → False)) ∨ (p5 → (p5 ∨ p3)))) := by
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
theorem thm_5_vars_45957092998996517751288947204 : (((p5 → (((p2 → p2) → (p2 ∨ p2)) → (p1 → ((((((True → p5) ∧ p1) → (p4 → True)) → p5) ∧ (True ∧ False)) ∨ p3)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53208498011011022838475332638 : ((((((p2 ∧ (p3 ∧ False)) → p3) → p2) ∧ ((p3 ∧ p1) → True)) ∨ ((p2 ∨ ((p2 ∨ p5) → p3)) ∨ (p1 ∨ ((p2 ∨ p4) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612363529043900192127016468559 : (((((p2 ∨ ((False → ((p1 → ((False ∨ ((p4 ∨ p2) ∧ (True → p4))) ∧ (p5 ∨ p3))) ∨ (False ∧ p1))) → p3)) ∧ (p2 ∨ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219082719566757669864105154205 : ((p5 ∧ (p4 → (True ∨ p5))) → ((p4 ∨ (False ∧ (((p1 ∨ ((p4 ∨ p2) ∨ p2)) ∨ True) ∧ (True ∨ p5)))) ∨ (p2 → ((p1 → p5) → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171779175035597976685678309407 : (((((p1 ∨ p4) ∧ ((((p2 → p4) → p5) ∨ p4) ∨ p2)) ∧ (p2 → True)) → p1) ∨ (p5 → (p1 → (False → ((p4 ∨ True) ∨ (p5 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662383061859554128189259120573 : ((((((p2 → p3) ∧ (((p5 ∨ p1) → p1) → p4)) ∨ (False ∧ ((p5 → ((((p2 ∨ p1) ∧ p1) ∨ p3) ∨ p1)) → p1))) → (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618432606215886059472992712630 : ((((((p3 → (p4 ∧ p5)) ∧ True) → ((p2 ∨ ((True ∧ (True ∨ (((p5 ∨ (p5 → False)) → p4) → (p2 → True)))) → p4)) ∧ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228213693946228572722123890276 : ((p5 ∧ (p1 ∨ p4)) ∨ (((((((p2 ∨ p1) → p1) ∨ (False → p2)) ∧ (p1 → (p5 → False))) ∧ (p4 ∧ p4)) → ((p4 → p2) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172607998826652516921992379913 : (((p4 ∨ (p4 → p1)) → (False ∨ (True → ((p3 ∧ (False ∨ (p5 ∨ p1))) → p4)))) ∨ ((((p2 ∧ (p5 ∨ p5)) → p1) → True) ∨ (p5 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65459643695899281901790811167 : ((p3 ∨ ((True → False) → (((p4 ∨ p1) ∨ False) ∨ (p1 ∨ (p2 → ((False ∨ p3) → ((p1 ∨ False) ∨ (True ∧ (False ∧ (p1 → p1)))))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_578699263139986651114789072162 : (((p3 → (p3 ∧ (p4 ∨ ((False ∧ p5) ∨ (p4 → ((p2 → ((p4 → (p5 ∨ p4)) ∧ (False ∧ (p2 ∨ ((p1 → True) ∨ True))))) ∨ p4)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654621107684424736105767783847 : (((((p3 → (((((p3 → (False → (p3 ∧ p5))) ∨ (True ∧ (p2 ∨ True))) ∧ (p1 → (p4 ∨ False))) → p4) ∨ True)) ∨ p4) ∨ (False ∧ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_200311332892318172270529098923 : (((p3 ∧ p5) ∧ (p1 → ((True → p2) ∧ p1))) → (False ∨ (False ∨ ((p1 ∧ ((p3 → True) → (True ∧ (p1 ∧ (p3 ∧ p3))))) ∨ (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160268206320651024573968114614 : (((True → ((False ∨ (p1 ∨ True)) ∧ ((((p2 ∧ p5) ∨ False) ∧ p5) → (False ∧ p4)))) ∨ (p2 → True)) → (((False ∧ p4) ∨ (p1 ∨ True)) ∧ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51869163139859425940894913990 : (((((((p1 ∨ True) ∧ p2) → p3) → (False ∨ (((p1 ∧ p4) → p5) → p3))) ∨ True) ∨ (((((p1 ∨ True) ∧ p1) ∧ p2) ∨ False) ∧ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694045971376681884007622144178 : (((((((True ∧ p5) ∨ (p4 ∨ p4)) ∧ (True → p3)) ∧ (p1 ∨ (p4 ∨ False))) ∨ (p5 → ((p1 ∨ (p5 → p5)) → ((p2 ∧ p3) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64264075226894149636510019571 : ((False ∨ (p5 ∨ ((p4 ∧ ((p3 → (p1 → False)) ∧ p1)) ∨ (((p2 ∧ (p3 ∧ True)) ∧ ((p1 ∧ ((p1 ∧ p3) → p5)) ∨ p3)) ∨ True)))) ∨ p3) := by
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
theorem thm_5_vars_313963819593763838577688126247 : (p3 ∨ ((((p1 ∨ (p1 ∨ p2)) ∨ ((p3 → (p4 ∨ (((p1 ∨ p2) ∨ p3) ∨ False))) ∨ (False → p3))) ∨ (p2 ∨ (p3 ∧ False))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739101467117146043620824854019 : ((((p3 ∧ p5) ∨ (((p5 ∧ (False ∧ (False ∧ (p5 ∨ ((p5 ∨ p2) → ((p5 ∧ p2) ∨ ((p4 ∨ p5) → p1))))))) ∧ True) ∨ (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166660557374114189431383415766 : ((p1 → (p2 ∨ (((p3 ∧ (((p4 ∧ (p2 → p4)) ∨ (p1 ∧ p2)) ∧ p1)) → True) → False))) ∨ (False → ((True ∧ False) ∨ (False → (p3 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78189583504619602057999558481 : (((p2 → (((p3 ∧ ((p5 → (p1 ∧ p1)) → (p5 → (p2 → (False ∧ p3))))) ∨ ((p1 ∧ (p5 ∨ p3)) ∧ p4)) ∨ (False → False))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((p3 ∧ ((p5 → (p1 ∧ p1)) → (p5 → (p2 → (False ∧ p3))))) ∨ ((p1 ∧ (p5 ∨ p3)) ∧ p4)) ∨ (False → False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124354059940875137541074273861 : (((((p4 → p2) ∧ (p5 → (p1 ∧ p2))) ∨ p5) ∨ (p4 ∨ (True → ((((((p4 → p5) ∧ p4) ∧ p2) ∨ p2) ∨ p5) ∧ p3)))) → (p3 → p3)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305187621749830083690046629028 : (p1 ∨ ((True ∧ (p5 ∧ (p1 ∨ (p5 ∧ (True ∨ ((((p2 → p2) → True) ∧ (p2 → (True ∨ p4))) ∨ False)))))) ∨ (p1 ∨ (False ∨ (False → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



