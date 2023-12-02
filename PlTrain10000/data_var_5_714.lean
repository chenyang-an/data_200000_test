variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330377988457304342016689207505 : (True → (p2 ∨ ((((True ∧ (((p4 → p5) → p3) ∨ (True ∧ (True ∨ True)))) ∨ False) ∨ p4) → ((p1 ∨ (p1 → p4)) → (p2 → (p3 ∨ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h29 =>
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344133340581273211677709381611 : (p2 → (False ∨ ((p3 ∨ ((True → p3) ∧ p2)) → (p3 ∨ (False ∧ ((p4 → ((((p3 → p4) → (p3 ∧ True)) ∧ (p4 ∨ p3)) ∧ p3)) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41060784405285774464277881064 : ((((p1 ∧ (p2 ∧ ((((p4 ∧ p3) ∨ (False → (((p4 → True) → p4) ∧ p2))) ∨ (p4 → p3)) ∨ (p3 → p3)))) → (p3 ∧ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40482018911571661321237894091 : (((((p1 ∧ p4) ∨ (((p3 ∨ (p2 → True)) ∧ (False → (((False ∨ p5) ∨ False) ∨ p3))) → (((p1 → p3) ∨ p1) ∧ True))) ∨ p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112346011401370914848564515092 : (((p5 → (True ∧ ((p1 ∨ ((p5 ∧ p3) ∧ True)) ∧ ((p4 ∧ ((((p2 ∧ p3) ∨ (p5 ∨ p4)) ∨ p2) ∧ p5)) → p3)))) ∨ True) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748596650001431527247641937373 : ((((p3 → p1) → ((((p3 ∧ p1) → (p3 ∨ p5)) ∧ p2) ∧ ((((p4 ∧ (p4 ∨ p3)) ∧ False) ∨ p1) ∧ (p2 ∧ (False ∧ (p2 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356341633256047475061024324531 : (p5 → ((((((p3 → p5) → p3) ∨ p4) ∧ ((p5 ∨ (p3 ∨ p2)) ∧ p1)) ∧ p3) ∨ (((p1 ∨ p1) → (((p3 → p2) ∨ p1) ∧ p5)) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256141675407030667901946769134 : ((True ∨ p5) → (p1 → (((False ∧ True) ∧ (True ∧ True)) ∨ ((((False → ((((p2 ∨ p4) → (p5 ∨ False)) ∧ p4) ∨ p2)) ∨ p3) → p2) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607857489218934998937828010545 : (((((p5 ∨ (p1 ∧ ((p5 ∨ (False ∨ (False ∧ ((p4 ∧ (p2 ∨ p3)) → (p1 → (p5 ∨ False)))))) ∧ ((False ∧ p3) ∧ p2)))) ∧ p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_352623116713799090792063209413 : (p4 → ((True ∧ p1) ∨ ((((p2 → False) ∨ (True ∨ p1)) ∧ True) ∧ (((p1 ∨ (p2 → p5)) ∧ (False ∨ (False ∨ ((p4 → p5) ∨ p1)))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185279289712941560745342475713 : ((p2 ∧ ((((p4 ∧ p5) ∨ (p1 → (p5 ∧ p2))) ∨ False) ∨ True)) ∨ (True ∨ (False ∧ ((((p1 ∨ False) ∨ p3) ∨ (True → (p5 → True))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253805108513839819135803803964 : ((p1 ∧ p2) → (((((p3 → (True ∨ True)) ∨ (p5 ∨ p1)) ∧ (True ∨ p3)) → (p5 ∨ p4)) ∨ ((((p1 → True) ∧ (p2 ∨ p1)) → p5) ∨ p1))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768976422352609152389980586146 : (((p5 ∧ (((p4 ∨ p2) ∨ p3) ∧ (((p3 → (p3 → (p4 ∨ (p4 ∨ p4)))) ∨ (True ∨ (True ∧ p1))) ∧ ((p4 → p2) ∧ (p2 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133884557945753813883662691333 : (((p5 ∧ (False ∨ (((p3 ∨ (p3 ∧ (p1 ∧ (p4 ∨ (p4 → p3))))) ∧ ((p1 ∨ (p1 ∨ True)) ∨ True)) ∨ True))) ∧ p3) ∨ ((p3 ∧ p2) → p3)) := by
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
theorem thm_5_vars_664907062695372388757986656641 : ((((p3 → (((((True → p4) ∧ False) ∨ False) → (p3 → (p3 ∨ ((True ∧ (((p4 ∨ p1) ∨ False) → p1)) → p5)))) ∧ p1)) → (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354549166617344699272836221020 : (p5 → ((p4 → (((p5 → p1) → (False ∧ (((True ∨ p2) ∨ p2) ∧ (p3 ∧ False)))) → ((False → (False ∧ p3)) ∧ ((p2 → False) ∨ p5)))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78753977442689885252829347894 : (((((((p3 ∧ p3) ∨ p1) ∨ True) ∨ ((False ∨ p1) ∧ p4)) → ((((p2 → True) → (False ∨ p1)) → (False → p2)) → p3)) ∧ (p5 → p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∧ p3) ∨ p1) ∨ True) ∨ ((False ∨ p1) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p2 → True) → (False ∨ p1)) → (False → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114622907082980392280957113818 : ((((((p4 ∨ p5) ∨ p5) → (((p5 ∧ p1) ∧ (p1 ∧ True)) ∨ (p5 → True))) ∧ True) ∨ (p4 ∨ (p5 → (p2 ∧ (False ∨ p1))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665133768460294280662330149642 : ((((p5 → (p5 → ((p3 → (((p1 ∨ (p5 → p2)) ∧ ((False ∧ True) ∧ False)) ∧ p1)) ∨ (((p3 → p5) ∧ True) ∧ False)))) → (p1 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41912546253764475741481247824 : (((((p5 ∧ p2) → False) → (((p3 ∧ ((p5 ∧ (p2 ∨ (p5 ∧ p2))) → False)) ∨ ((p4 ∧ ((p1 ∧ p5) ∨ p4)) ∧ True)) ∧ False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261350652183541395683573567772 : ((p5 → False) → ((True → p5) → ((p4 ∧ ((p4 ∧ ((((False ∧ p2) → p4) ∨ (p2 → False)) → p4)) ∧ (p5 → ((p5 ∨ p4) ∨ p1)))) ∨ p2))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202501794898801051521325081386 : ((((p5 ∨ False) ∨ True) ∨ (p5 ∨ p4)) ∧ ((((((True → p4) ∧ (p2 ∨ p3)) ∧ p3) ∨ (False ∨ (((p3 ∨ p5) ∨ p1) ∧ p1))) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134892348508515551790333160566 : (((p4 → (p5 → ((((p5 → (p1 ∨ p5)) ∧ (p4 ∨ True)) → (p3 → (p3 ∧ (p5 ∧ (p1 ∨ p3))))) ∨ p2))) → p4) ∨ (False ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52359340595891942943636688473 : (((((p5 ∧ (((False ∧ p4) ∨ p1) ∨ (p3 ∧ False))) ∧ False) ∨ (p1 ∧ p2)) ∧ ((p3 ∨ p5) → (p4 → (((p5 ∨ True) → p3) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177910892098206808016778368243 : ((((p5 ∧ ((True ∧ p4) → (p5 ∨ (p1 ∨ p2)))) → (True → p1)) ∨ p2) ∨ ((((False ∧ (False ∧ (True ∨ (p1 ∧ False)))) → p5) ∧ p1) → p1)) := by
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
theorem thm_5_vars_57306023858280988532471178995 : (((True ∧ (True ∧ p1)) ∨ ((((p2 → ((p3 ∨ (False ∨ p4)) ∨ p1)) → ((False ∨ (p1 → (p3 → False))) ∧ p4)) ∧ p5) ∨ (p3 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678160896339442751891057294858 : (((((((p2 ∧ ((p4 → p2) → ((p5 ∧ p1) ∧ False))) ∧ p5) → p4) → (((True ∧ p2) → p4) ∧ False)) ∨ (False ∧ (p5 ∨ (p4 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323984142857831815199998829760 : (p5 ∨ (((p3 ∧ ((((p1 ∧ True) ∨ (True → False)) ∨ (p1 → p1)) → False)) ∨ True) ∨ (p3 ∨ ((p3 → False) ∧ (((p5 ∧ True) → False) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195724720103653555782982897276 : (((p3 ∨ p3) ∨ (((p2 ∧ p3) ∨ True) ∨ p5)) ∧ (False ∨ (p3 ∨ ((p5 → ((p1 ∧ p1) ∨ (False ∨ (p5 ∨ False)))) ∨ (p4 ∨ (p2 ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200365969858396789354297808790 : (((p2 → False) ∧ (p5 ∨ (True ∨ (False ∨ p1)))) → ((False ∨ (True → ((((p5 → ((p1 ∧ False) ∧ (p3 ∧ p5))) → p5) ∧ True) ∨ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142461940720972006524552777862 : ((p5 ∧ (((p4 ∨ False) ∨ ((((p4 → p2) ∧ False) ∨ p4) ∨ ((False ∨ (p1 ∧ p1)) → p1))) ∧ ((True ∧ p2) ∨ True))) → ((True → p1) → p1)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h28 := h2 h27
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h31 := h2 h30
          -- One of the premise coincides with the conclusion.
          exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h37 := h2 h36
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h40 := h2 h39
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203925414962485051355758684432 : ((p2 → ((p1 ∨ (False ∨ p1)) ∨ p2)) ∧ ((p1 ∧ False) ∨ ((((p4 → ((p4 ∨ (p2 ∧ p5)) ∨ p3)) → True) ∨ ((False ∨ p2) ∧ p3)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78553344692408174830758931822 : ((((False ∨ (p1 ∨ ((p3 ∨ p3) ∨ ((p4 ∧ (((True ∧ p4) ∨ ((p5 → p3) → (True ∧ False))) ∨ p5)) ∨ True)))) → p1) ∧ (p5 ∨ True)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (False ∨ (p1 ∨ ((p3 ∨ p3) ∨ ((p4 ∧ (((True ∧ p4) ∨ ((p5 → p3) → (True ∧ False))) ∨ p5)) ∨ True)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ (p1 ∨ ((p3 ∨ p3) ∨ ((p4 ∧ (((True ∧ p4) ∨ ((p5 → p3) → (True ∧ False))) ∨ p5)) ∨ True)))) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180269236433645816711836393039 : (((False → ((p5 ∧ (False ∧ (p3 ∧ (False → (False ∨ p3))))) ∨ p1)) → p1) → ((p2 → (p3 ∨ (False ∧ p1))) ∨ ((p5 ∨ True) ∨ (p1 ∧ p3)))) := by
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
theorem thm_5_vars_632828012417596230438829562538 : ((((((p5 ∨ (((p4 → p5) → ((p2 ∨ ((p4 → False) ∧ p3)) ∨ ((p2 ∨ p3) ∨ (p4 → p4)))) ∨ p1)) ∨ p2) ∧ (p1 ∨ False)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2993462406039359306027075847 : (((False ∨ p4) ∧ True) → (((p1 ∧ p2) ∨ (p5 ∧ ((p5 → p3) ∨ p5))) → ((p4 ∨ p5) → (False ∨ (((False ∨ True) ∨ False) ∧ p4))))) := by
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
    cases h2
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
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
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
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
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
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
          -- One of the premise coincides with the conclusion.
          exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h1.left
      let h30 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
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
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h1.left
        let h38 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h39 =>
          -- False on the left can always be used.
          apply False.elim h39
        case inr h40 =>
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
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h1.left
        let h43 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h44 =>
          -- False on the left can always be used.
          apply False.elim h44
        case inr h45 =>
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
          -- One of the premise coincides with the conclusion.
          exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793603443677726471019569843182 : (((True → (p3 ∨ (p2 → ((((p1 ∧ p2) ∧ (p4 ∨ p5)) ∧ ((p1 → p5) ∨ (((p4 → False) → ((True ∧ False) ∨ p1)) ∧ True))) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614480378295846612425026605034 : (((((((((p1 → (True → p2)) ∧ p5) ∧ (((p2 → p3) → p3) → (p1 ∨ p4))) ∧ p5) → p3) ∧ (p4 ∨ ((True ∧ p5) ∨ p4))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113874476814026543302772033589 : (((((((p1 → (p3 ∨ p2)) ∨ True) ∧ ((p5 ∨ False) ∨ (p5 → (p2 ∨ p2)))) → (p4 ∨ p5)) ∧ True) ∧ (p4 ∨ (p4 ∨ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43809263597337023454905448529 : ((((p1 → (p4 → ((((False → p1) ∨ True) ∧ True) → (p5 → ((((p1 ∨ p4) → (p2 ∧ p2)) → False) ∨ (p1 → True)))))) → p2) → p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p4 → ((((False → p1) ∨ True) ∧ True) → (p5 → ((((p1 ∨ p4) → (p2 ∧ p2)) → False) ∨ (p1 → True)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308458024707084580719894110230 : (p2 ∨ (((((p3 ∨ True) ∧ (((((False ∨ (p2 → (True ∨ p5))) → p5) → (True → (p1 → p5))) → p5) → p4)) ∨ p5) ∨ (True ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38256779460540938378453482068 : (((((p2 → p4) → ((((p3 ∧ False) ∨ (p2 → (p4 ∨ False))) ∨ (p1 ∨ (p3 ∧ p5))) ∨ p5)) ∧ (p5 ∧ ((p1 ∨ p1) → p5))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350145913664728428080865169717 : (p4 → (((((False → p1) ∧ p1) → (p5 → ((p1 ∧ (p3 ∨ p2)) → p1))) → ((p1 ∨ (p1 → p2)) ∨ (p1 ∧ (False ∧ (p4 ∨ False))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40683203218729031766045081756 : (((((p3 ∧ (((p3 ∨ ((False ∧ p5) ∧ (False ∨ False))) → (p2 → False)) ∨ ((p4 ∧ p1) ∧ False))) → ((False ∨ True) → False)) → p5) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665025199786608660951853104567 : ((((p4 → (((p3 → p1) → (p2 ∨ True)) → (p1 ∨ ((p4 → (p2 ∨ True)) ∧ ((p5 ∧ p1) ∧ (p3 ∧ (p5 ∧ p5))))))) → (True ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226187240605516078105075450263 : (((p1 ∨ p5) ∨ p1) ∨ ((p4 ∧ (p5 ∨ (((p4 ∨ p3) ∧ ((p1 ∨ p5) ∧ False)) → False))) ∨ (((p5 → p5) ∨ ((p3 → p3) ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624059234406373173378727346821 : ((((p2 ∨ (((True → p5) ∨ (p5 → (p3 ∧ (p2 → p4)))) ∨ ((p5 ∧ p4) → (p2 ∧ (((False → (p1 ∨ False)) → p1) ∨ p2))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352277629969136343382921629022 : (p4 → (((True ∨ True) ∧ (True → True)) → ((p2 → False) → (((((p2 → p2) ∧ ((False ∨ True) → p3)) ∨ (p2 ∨ (p3 → p3))) ∧ True) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136249194069420072244620366563 : (((p2 ∨ (((p3 → p1) ∧ p5) → False)) ∨ ((p2 → (p2 → (p5 ∨ p3))) → (((p3 → (False ∨ p4)) ∧ p5) ∨ p4))) ∨ (False → (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342536746612224774908873576361 : (p2 → (((p5 ∨ (p5 ∧ ((False ∨ ((p2 → p3) → p5)) ∧ p2))) ∨ p2) ∧ (p5 → (((p2 ∧ p2) ∨ (p2 ∨ (p4 → (p2 → True)))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115478770001339793206149395951 : (((p2 → (p1 ∨ (p5 ∧ ((p1 ∧ p3) → True)))) ∨ (((((p3 → p1) ∨ p1) ∨ (True → ((p4 ∨ p3) → True))) → p3) → p3)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p1) ∨ p1) ∨ (True → ((p4 ∨ p3) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307726800028419141180466755323 : (p1 ∨ (p3 → ((((p5 → (p3 ∨ (False ∧ (p5 ∧ (p4 → (((p3 → True) → p1) ∨ (p5 ∧ p5))))))) → (p5 ∧ (p1 ∧ p2))) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807305230502351690805716499017 : (((p4 → ((p2 ∨ (((p4 ∧ (((p1 → p1) ∨ p1) ∧ p3)) ∧ p4) ∧ p5)) ∧ (((((p4 → (p4 ∨ p3)) ∧ False) → False) ∧ False) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309246171432838297311444409272 : (p2 ∨ (((False ∨ (p5 ∧ (p2 ∨ p1))) ∨ ((False ∨ (False → False)) ∨ (False → (p5 ∧ (p2 ∨ (p1 ∨ (p3 ∧ (p3 → p1)))))))) ∧ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711855863906942466040772667112 : (((((p1 ∧ (False → (False ∧ p1))) ∧ p4) ∨ (((p3 → (p4 ∧ p1)) → ((p3 ∨ p1) → (p5 ∨ ((p3 ∨ False) ∨ (False → True))))) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42076336257806899469787907466 : ((((p1 → False) ∨ (p2 → ((False ∨ ((p4 ∨ ((((p5 ∧ False) ∨ True) ∧ p3) ∨ p2)) → (p2 → (p5 ∧ (True ∧ True))))) ∧ p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686811349943236261810192144347 : ((((p3 ∧ (True → (False ∨ ((p3 ∧ (((p2 ∧ False) ∨ ((p3 ∨ p2) ∨ p5)) → p4)) ∧ p4)))) → ((False ∧ ((p3 ∧ p3) → p5)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654789675247886115812655235805 : ((((((p5 ∨ (p3 ∧ (((p2 → p2) ∧ (((p3 → (True ∧ (False ∨ (p1 ∨ False)))) ∨ p2) → True)) → p4))) → p1) → p4) ∨ (p3 → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_750020120838735110962033051875 : (((True ∧ ((((p1 ∨ ((p1 ∧ (p1 → True)) ∨ p4)) ∧ p1) → (p1 ∧ ((p5 ∧ p1) ∨ ((True → (p5 → p5)) ∨ (p1 ∧ p5))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678801927318540471605818311065 : ((((True ∧ (True ∧ (((((p2 → p4) ∨ False) ∧ (True → p2)) ∧ ((True ∧ (p1 ∧ p3)) → p1)) → p1))) ∨ (((p4 ∧ p1) ∧ False) → True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_114022994389064448748304054744 : ((((p4 ∧ (((True ∧ ((True ∧ (p2 ∨ (p2 → ((p1 ∨ p4) → p3)))) ∨ p2)) → p3) ∨ p1)) ∨ False) ∨ ((False → True) ∨ p1)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444032732567951761902494316427 : (((((False ∨ p5) ∨ (p5 ∨ (p5 ∧ (p4 ∨ ((((p3 ∧ True) ∧ True) → ((p3 → p4) ∧ p2)) ∨ (False → p2)))))) ∨ ((True → False) → p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184955335238769972506406608491 : ((((p5 → p5) ∨ p2) → ((p5 ∧ ((p3 → p3) ∨ p3)) ∧ p5)) ∨ (p1 → (((((p5 ∧ p3) → p1) ∧ p2) → (p1 ∨ (False ∧ p2))) ∧ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126445861257801565478735713997 : ((p2 ∧ ((True → (((p2 → (p4 → (False ∧ p3))) ∧ ((p4 ∨ True) ∧ (((p5 → (p1 ∨ p5)) → True) → p4))) ∨ False)) ∨ False)) → (p3 ∧ p5)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h13 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h14 := h8 h13
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h19 : ((p5 → (p1 ∨ p5)) → True) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h21 := h11 h19
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h22 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h23 := h8 h22
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h33 := h31 h32
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h40 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h41 := h35 h40
        -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
        have h42 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h41, we can now drive its conclusion.
        let h43 := h41 h42
        -- We need to get the left conjuct of h43 based on <expert-advice>.
        let h44 := h43.left
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h46 : ((p5 → (p1 ∨ p5)) → True) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h48 := h38 h46
        -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
        have h49 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h35, we can now drive its conclusion.
        let h50 := h35 h49
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h51 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h48
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h52 := h50 h51
        -- We need to get the left conjuct of h52 based on <expert-advice>.
        let h53 := h52.left
        -- False on the left can always be used.
        apply False.elim h53
    case inr h54 =>
      -- False on the left can always be used.
      apply False.elim h54
  case inr h55 =>
    -- False on the left can always be used.
    apply False.elim h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111607919193975678026159184488 : ((((((((p4 ∨ (p1 → (p1 ∨ p3))) → p1) → (((p5 ∧ p3) ∨ p4) ∨ ((p4 → p3) ∨ p5))) ∨ True) ∨ False) ∨ p3) ∨ False) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_337038712623905751489468137399 : (p1 → (((((p5 ∨ ((p1 ∨ p2) ∧ ((p4 ∨ p4) ∧ (p3 → p1)))) ∨ p5) ∧ ((((True ∧ p3) ∨ False) ∧ p2) → False)) ∧ p2) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147145139638095564847195734350 : (((p1 ∧ (((p2 ∧ (p2 → ((False ∨ p1) ∨ True))) ∨ ((p1 ∧ True) → p4)) ∨ (False ∨ (p4 → p3)))) ∧ p3) ∨ ((p5 ∨ p4) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141056212318301493611824080235 : ((((p1 → (p3 → (p2 ∨ (False ∨ False)))) ∨ p4) ∨ (p2 ∧ (((p1 ∧ p5) ∧ p5) ∨ (p2 → ((False ∧ False) ∧ p2))))) → (p5 ∨ (p1 ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300282414886918884700323071527 : (False ∨ ((p3 → (p4 → (False → (p5 ∨ (p4 ∨ (((p3 → p1) → False) → (((p1 ∨ False) → True) ∨ (p3 ∨ (p4 ∧ p5))))))))) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341668669901397704462236451593 : (p2 → ((((p3 ∧ ((p3 ∨ True) → (p5 ∨ ((p1 ∧ (p3 ∧ ((False → (p1 ∨ p2)) → True))) ∨ (False → p4))))) ∧ False) ∨ p5) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148188143916116565692975659873 : ((((p1 ∨ (p5 → (False ∨ (True → (p1 ∨ p3))))) → ((p3 ∧ p2) → (False ∧ True))) ∧ ((p5 ∨ False) ∨ p1)) ∨ (((p1 ∧ p4) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114465821170647043267437484092 : ((((False ∨ (p2 ∨ ((p3 ∨ p2) ∨ (p3 → ((p5 ∧ p1) ∧ (p1 ∧ (p4 → p2))))))) ∨ p4) → ((p3 ∨ p3) ∨ (False ∧ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54083797691011267990868594395 : ((((p3 ∧ p3) ∨ ((True ∧ p2) ∨ (p1 → (p5 ∧ p5)))) → ((p1 ∨ (p1 → p4)) → ((p3 ∧ ((p3 ∨ p1) ∨ True)) → (p5 ∨ True)))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h47 =>
        -- Conjunctions on the left can always be decomposed.
        let h48 := h47.left
        let h49 := h47.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h54 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h56 =>
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- Conjunctions on the left can always be decomposed.
          let h61 := h60.left
          let h62 := h60.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161530249622441448436937856294 : ((p5 ∧ (((((p3 ∧ ((False ∨ (False → p1)) ∨ False)) ∧ p4) → p2) ∨ (True ∨ (False ∧ p4))) ∨ p2)) → (((p1 ∨ (p3 ∨ True)) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
  case inr h11 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95635131110140535577444247050 : ((p5 ∧ ((((p4 ∨ True) ∧ p5) → False) ∧ (p3 → ((((p4 ∨ (((p4 ∧ True) ∨ (p1 → (p3 → False))) → p4)) → False) → p2) ∧ False)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ True) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134034167396532948275521578060 : ((((((((True → (False ∨ p1)) → p2) ∧ ((p2 ∧ p3) ∨ False)) ∧ (p4 ∧ p3)) → ((p5 ∧ p3) ∧ p1)) ∨ False) ∨ p4) ∨ (False → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192282549798558028853145464387 : ((((p1 ∧ p4) ∨ (((p1 → p4) ∨ p2) → p5)) ∧ p3) → (((((p1 ∨ (p1 ∨ True)) ∧ (p2 ∧ (True ∨ p5))) → p5) → (p1 ∧ p3)) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266214704702686153878382409764 : (True ∧ (p4 → ((p2 ∨ p1) ∨ (((True ∧ (((p5 ∧ p2) ∨ p1) ∧ p3)) ∨ p1) → (((False ∧ (False → True)) ∨ ((p3 ∧ p3) → p3)) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327012137211902471454302785346 : (True → ((((False ∧ False) ∨ (((p3 → p2) → p5) ∧ ((p1 ∨ ((p4 ∨ True) → p5)) ∧ p1))) → ((p4 ∨ (p4 ∧ False)) ∨ (p2 ∨ p1))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184445907477476748032220461765 : (((p2 ∧ ((p3 ∨ ((p3 → p1) → p1)) ∨ p2)) ∧ (p4 ∨ True)) ∨ (True ∧ (p1 ∨ ((True ∨ (p1 ∧ p3)) ∨ ((p3 ∧ (p5 → p1)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694088239371644379078551662060 : (((((p1 ∨ (p1 ∧ (((p5 → p1) ∨ p2) ∧ True))) ∨ ((p2 ∨ True) ∨ p3)) ∨ (p5 → (((p2 ∧ p4) → p4) → (p3 → (p5 ∨ p2))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58438695236959929091593061249 : (((p3 ∨ True) ∧ (p4 → ((False ∨ p4) ∧ (p2 ∨ (((p3 ∨ p1) ∧ p4) ∨ (False → (p5 ∧ ((True ∧ (p4 ∧ p1)) ∧ (p2 → False))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228106440299647927478734343987 : ((p4 ∧ (p3 ∨ p3)) ∨ (((p4 ∨ p3) ∨ p1) ∨ (((p5 → p1) ∧ p2) ∨ (p5 ∨ (p1 → ((p3 ∧ (p4 → ((False → False) ∧ p2))) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328615160242014805681115358374 : (True → (((((p2 ∨ True) ∨ p2) ∨ ((p4 → p2) ∨ p4)) → ((False ∧ p3) ∨ True)) ∨ (((((False ∧ p4) ∨ (p3 ∨ p5)) ∨ p3) ∧ True) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
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
  case inr h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45932446302119045651688795481 : (((p4 → (p3 → ((p5 ∧ ((p4 ∨ p2) ∧ ((p1 ∨ (p2 → (p4 ∨ ((p5 → p3) ∧ True)))) ∨ p4))) ∧ ((p3 ∨ False) ∨ p3)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62376258742585915577581119366 : ((p3 ∧ ((((p4 ∧ p2) → p4) ∨ (((((p3 ∨ p3) ∨ p4) ∧ False) → p2) ∧ False)) ∧ ((False ∧ p2) ∨ (p4 ∨ (p2 → (False ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355851540321547482905901966883 : (p5 → (((((p3 → p2) ∨ (p3 ∨ True)) → ((((p2 ∨ p4) ∨ (False ∨ p4)) → p1) ∨ (True ∧ p3))) → (p1 ∧ False)) ∨ (p2 ∨ (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156886619581306438225865608340 : (((((((p4 → (((True ∧ p4) → p1) ∨ (p5 ∧ p5))) → p4) ∨ p2) ∨ (p2 ∧ p2)) ∨ True) ∨ False) ∨ (True ∧ ((p1 ∧ (p4 → p2)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251962227321498504201024599069 : ((p4 → False) ∨ ((((((False ∨ p3) ∧ (True ∧ ((False ∨ p5) ∨ (p1 → (True ∧ ((True → False) → True)))))) ∨ False) ∧ p5) ∨ (True ∨ True)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708973787511215064533627806363 : ((((((p3 ∧ p2) ∧ (p2 → False)) → (p5 → True)) → ((p2 → False) ∨ (False → (p2 ∨ ((p1 ∧ True) ∨ (p2 → ((p4 → False) ∨ p2))))))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113926367886883090256502269391 : ((((((p1 ∨ ((False ∨ (p5 ∧ p4)) ∨ True)) → (p1 ∧ p1)) ∨ False) ∨ (p2 ∧ (p4 ∨ (True ∨ p5)))) ∧ (False ∨ (True ∨ p5))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14586052789177893753612416408 : ((((True → (((p2 → (p5 ∨ p3)) ∧ False) ∧ (p4 ∧ (p2 ∧ (p2 → ((p4 → (p2 → (p4 → p4))) ∧ True)))))) ∨ p1) ∨ (True ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149656618105652463405858697100 : ((p4 ∧ ((p4 ∨ p4) ∨ ((((((p1 ∨ (False → p1)) → ((True → True) ∨ p4)) ∧ p3) ∧ True) ∨ p5) ∨ p4))) ∨ (((p3 → True) ∨ p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322235950028723961082805745470 : (p5 ∨ ((((((p5 → p4) ∨ (p3 → (p1 → (p2 ∨ (p1 → ((p2 → False) → ((p3 ∧ (False → False)) ∧ p2))))))) ∧ p5) ∧ True) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113735833970959278457290358494 : ((((p5 ∨ (False ∨ ((True ∨ ((p5 ∨ False) ∧ p5)) ∧ (p4 → (p4 → p3))))) ∧ (p5 → ((p2 ∨ p4) → p4))) → (p5 ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69144862189192122683758234463 : ((p5 → ((p2 ∨ ((((False → (p3 → False)) → (p4 → p4)) ∨ p3) → ((p1 ∧ p2) ∧ ((p3 ∧ False) → p1)))) ∨ ((p5 ∧ p3) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118618981728765860631323085007 : ((p4 ∨ ((((p3 ∨ p5) ∨ ((p2 → p2) → (p2 ∨ True))) ∧ p4) ∨ (True → (p4 ∨ (((p5 ∧ (True ∨ p3)) ∧ p4) ∨ p2))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725800293710509798058707069032 : (((((p4 ∨ p1) ∧ True) ∨ ((True → ((((p4 ∨ (False ∧ p1)) ∧ p3) ∧ p5) → ((((False ∨ p1) ∨ p1) ∨ True) ∧ (True → p5)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632810044266222205231137096325 : (((((((((True ∧ False) ∧ True) ∨ (p1 ∨ p5)) → ((((True ∨ p4) ∧ p2) ∨ (p1 ∧ p2)) ∧ (p3 ∧ p5))) ∨ p1) ∧ (p1 → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88971627055035360315259077949 : (((p5 → (p4 ∨ (p2 → p2))) → (((p5 ∧ (((p4 ∧ ((p1 → True) → p4)) ∧ False) ∨ p5)) ∨ ((True ∨ p3) → p5)) ∧ (p4 ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p4 ∨ (p2 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



