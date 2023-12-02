variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112025305845802164379285418810 : ((((True → (False ∨ True)) ∧ (((((p4 → (((p1 ∨ p5) ∧ p5) ∧ p5)) ∧ p4) ∨ (p2 ∧ False)) ∨ (p4 ∧ p2)) ∧ p4)) ∨ p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238287629010095173485901741005 : ((True ∨ p5) ∧ (p2 → ((p5 ∨ ((True → (((((p3 ∧ False) ∨ (p4 → p5)) ∨ (True → (True ∧ p4))) → False) ∨ (p3 ∨ p2))) ∨ p2)) ∨ True))) := by
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
theorem thm_5_vars_801568380762793521751308772666 : (((p2 → (((p5 ∧ p1) ∨ (p4 ∨ (p4 → p1))) ∨ ((True ∨ (((p3 ∧ p2) ∨ (False ∨ p2)) ∨ True)) ∧ (p4 → (p2 → (p1 ∨ p2)))))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106537315563586316291779587178 : (((p3 ∧ ((False ∧ (p3 ∧ p5)) ∨ (p5 ∧ p2))) ∨ (p2 → ((False → ((p3 → ((p1 → True) → (p5 → p2))) → p2)) ∨ p2))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228591651297064254050067813625 : ((p1 ∨ (p5 ∨ p5)) ∨ ((p3 ∧ (p4 ∧ p4)) → ((p1 ∧ ((p3 ∧ p3) ∨ (True ∨ (p2 ∧ (p3 → p3))))) → (p5 ∨ ((False → p5) ∧ True))))) := by
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h27
      -- False on the left can always be used.
      apply False.elim h27
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135101429183119432897149958588 : ((((((p1 ∨ p5) ∨ p3) → p3) ∧ ((p3 ∧ ((p5 ∧ ((True ∧ False) ∧ p4)) ∨ (False ∧ p3))) ∧ p2)) ∨ (p5 ∨ p4)) ∨ ((p3 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180979647119380303238382085488 : (((p5 → p5) ∧ (p2 ∧ ((((True ∧ p3) ∧ p4) ∨ (p5 ∨ True)) → False))) → (p4 ∧ (True ∧ ((p4 ∧ (p3 ∨ (p5 ∧ False))) ∨ (p2 → p5))))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((True ∧ p3) ∧ p4) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (((True ∧ p3) ∧ p4) ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701109701881624305855794113268 : ((((((False ∧ False) → ((False ∧ (p1 → p2)) ∧ p4)) → p4) ∧ (p3 → (((p1 ∨ (p4 → (False → (p3 ∧ p5)))) ∧ (p2 ∧ p2)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61944739279609694743254587155 : ((p2 ∧ ((False ∧ (p2 ∧ (((((p1 ∧ p1) → True) ∧ (p2 ∧ p3)) ∨ False) ∨ (False → p5)))) ∨ (p5 ∧ ((p1 ∧ p2) ∧ (p4 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352493675072544719010622948420 : (p4 → ((False → (False ∧ p3)) → (p4 → ((((p4 ∨ (p1 ∨ (p3 ∨ (p5 ∨ p4)))) ∨ (False ∧ p1)) → True) → ((p1 → False) ∨ (False → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232242935133115471100684134806 : (((p1 → p4) → False) → (p4 → ((((p1 ∨ (p3 ∨ (True ∧ ((p2 → p3) ∨ (p2 ∨ p4))))) ∧ (((p1 ∨ p1) ∨ p2) ∧ p4)) ∨ p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784724831483968919360811788199 : (((p3 ∨ (p5 ∨ ((p4 → ((((p5 ∨ p5) ∨ (((p1 ∨ False) ∧ True) ∨ (p4 → (True ∨ False)))) ∨ False) ∧ (p2 ∨ (p2 ∧ p2)))) ∨ True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_725613116568047351404314749916 : (((((p4 ∧ True) ∧ True) ∨ (((p5 → (p1 → ((False ∧ p4) ∧ False))) → (True ∧ (p4 → (p5 ∨ p2)))) → (False ∧ ((p5 ∧ p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350240578504603558158528610901 : (p4 → (((p3 → p5) → (((p3 ∧ p4) ∨ True) → ((((True → ((p3 ∧ p3) → (((p2 ∨ p4) → p1) ∨ p4))) ∧ p1) ∧ p5) ∨ p1))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348272416943556555736826983863 : (p3 → (True ∧ ((p4 → (p1 ∨ p1)) ∨ ((p3 ∧ p4) → (((False ∨ ((((False → p5) → ((p2 ∨ False) ∨ p4)) ∧ False) ∨ p2)) ∨ p5) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55360153900291845055090391199 : (((p4 → ((False ∧ (p2 ∨ p5)) ∧ True)) ∨ (((p4 ∧ ((p1 ∨ False) → True)) → (True ∨ p5)) ∧ (p1 → (((p1 → p2) ∧ p2) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707473258572203897978629615267 : ((((((p5 ∧ False) ∧ p3) ∨ ((p5 ∧ p5) ∨ p3)) ∨ (((p4 → p2) ∨ ((p2 ∧ (p4 ∧ (True ∨ p2))) ∧ (p5 ∧ (p3 → p1)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47148026639737865169723016538 : ((((((True ∧ (p5 → p5)) → p3) → ((p2 ∨ p4) ∨ (((p5 ∧ p5) ∨ True) ∧ p5))) ∨ ((p5 ∧ (p3 ∨ p3)) ∧ True)) ∨ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244999290436023104629649665839 : ((p1 ∧ p4) ∨ ((((p1 ∨ (((p3 → p2) ∧ p1) ∨ p3)) ∧ (p4 ∨ True)) ∨ (False ∨ p2)) ∨ (((False → (True ∧ (p3 ∧ p5))) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53126841770898728113935010455 : ((((((p1 ∧ (((p2 ∨ p3) ∧ p5) ∧ p5)) ∨ p2) ∨ p1) ∧ p3) ∨ (True → (False ∧ (((p2 ∧ (False ∨ (p2 ∧ p3))) ∧ p2) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46337441417951789751292479028 : ((((((((False ∧ p2) ∨ False) ∨ False) → (False → p5)) ∧ (p5 ∨ (p1 ∧ p4))) ∧ (p3 ∨ (((False → p2) ∧ p4) ∧ p4))) ∧ (True ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61400853795624912371384318219 : ((p1 ∧ ((p4 ∧ ((p4 ∧ (p5 ∨ False)) ∨ (((True → (False ∧ p1)) → (False ∨ p5)) ∨ ((p4 → True) ∧ (p1 ∧ (p2 ∨ p1)))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451104439008334699391066437727 : (((((((p3 ∧ (p3 ∧ (p4 → p4))) ∧ (((False ∨ p2) → ((p5 ∧ True) ∧ p4)) ∧ p4)) → p4) → p4) ∨ (p1 → (p3 → (p1 ∧ p1)))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823739140353101265508348222901 : (((((((p4 ∨ p3) → p2) → p3) ∧ ((((p2 ∨ p2) ∧ (False → (False ∧ p1))) ∨ False) ∨ ((False → (p1 → (False ∧ p2))) ∧ p2))) ∧ p4) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : ((p4 ∨ p3) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h15 := h4 h11
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : ((p4 ∨ p3) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h20 =>
            -- One of the premise coincides with the conclusion.
            exact h16
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h17
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h26 : ((p4 ∨ p3) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h25
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h30 := h4 h26
    -- One of the premise coincides with the conclusion.
    exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123475164896010593821927842738 : (((((False → p2) → (((p2 ∧ (p4 → (True ∧ False))) → (p2 → True)) ∧ p3)) ∧ True) ∧ (((p3 → (p3 → p4)) → True) ∨ p4)) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974477412737272875536524126078 : ((((p1 → True) → (((p2 ∧ p5) ∧ (False ∨ ((p4 → p4) → ((p3 ∨ (p2 → (((p5 ∨ p5) ∨ True) ∨ (True → p4)))) → p5)))) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48104760930826827923225977482 : (((((False → p1) ∧ (p1 ∨ p5)) ∨ (p1 ∧ ((((((p2 ∧ ((p4 ∨ p4) ∧ True)) → p2) ∨ p5) ∨ p5) ∨ p1) → p1))) → (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610463067469672054571306518257 : ((((((True ∧ ((p4 ∨ (((p3 ∨ p3) ∨ p4) ∨ (False ∨ p1))) ∨ (p5 ∨ ((((True ∧ p1) → p1) ∧ p5) → p3)))) → False) → p1) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_37059466376370741210886554457 : (((((((((p3 ∨ p5) ∨ p5) ∧ p5) ∧ p5) ∧ ((True → (False → False)) ∨ (p3 ∨ (((p5 ∨ p3) ∧ p5) ∨ p5)))) ∧ p3) ∧ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354574265400806487320828908372 : (p5 → ((((((p2 → False) ∨ (True ∨ p1)) → (p4 ∨ (p4 ∧ ((p4 ∨ (p5 ∨ p3)) ∨ p2)))) ∨ (((False ∨ False) → p1) ∧ True)) ∧ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3437820884444143065041937999 : (True ∧ ((p2 ∨ (((True ∨ (((p5 → p3) ∧ p3) → p2)) ∨ (p3 ∧ p2)) ∧ False)) ∨ ((((p4 ∧ False) ∧ p5) ∨ (p5 ∨ True)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_157650088131893171461916719065 : ((((((p5 → (True ∧ p4)) ∨ (p3 → p5)) ∨ (p2 ∨ (p3 → p1))) ∧ p3) ∨ (True ∧ (p2 ∧ False))) ∨ (((p4 ∧ (p5 → p3)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245674288900832273154983111538 : ((p3 ∧ p1) ∨ ((((p2 ∧ False) ∨ p4) ∨ p4) ∨ (((((p5 → p4) ∧ p1) → (False ∨ (False ∨ p4))) → p4) → (False → (p4 ∨ (True ∧ p1)))))) := by
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
theorem thm_5_vars_55641293564107776443245235125 : (((((p2 ∨ p2) ∨ p5) ∧ p1) ∧ (p2 → (((p5 ∨ ((True ∧ p4) → p3)) ∨ (False → True)) → ((p4 → (p1 ∧ (p1 ∧ p2))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57808828063121111558824001906 : (((p2 ∧ (p5 ∨ p1)) → (((p4 ∨ False) ∨ p4) ∨ (((((((p2 → p2) ∨ p2) ∨ (p1 ∧ (p1 ∧ p1))) ∨ p3) → p5) → p2) ∨ p1))) ∨ p5) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61033857404967661377405881660 : ((False ∧ ((p3 → ((p5 ∧ False) ∨ (True ∧ (p5 → (((False ∧ (True ∧ ((False ∨ (False → p4)) ∨ p5))) ∨ p3) ∨ False))))) ∧ (p2 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340830709542911838883462270122 : (p2 → ((((p3 → (((p2 ∨ (True → p4)) ∧ p4) ∨ (True ∨ (p2 ∧ (((False ∧ p2) ∧ p5) ∨ (True ∨ p4)))))) ∨ p3) → (p3 ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137306454835818994730793621317 : ((p2 ∧ ((((p4 ∧ (False ∧ (((p4 → p4) ∨ (p2 → p4)) ∧ False))) ∧ p4) ∨ p5) ∧ (((p2 ∨ p5) ∨ p1) → p3))) ∨ (False → (p4 ∧ p1))) := by
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
theorem thm_5_vars_326000656951738674419155426042 : (p5 ∨ (True → (((False ∨ True) ∧ (((p4 ∨ p2) ∨ p5) ∨ (p5 → p1))) → ((((p4 ∧ (((p3 → p3) ∨ True) ∧ False)) ∧ False) ∨ True) ∨ p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_428127536851307709484797680343 : ((((((((p3 ∨ (p4 → (((p5 → (False ∨ False)) ∧ (p3 → p3)) ∨ (p4 → p1)))) ∨ p1) ∧ (p1 → False)) ∧ p3) → False) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164523331222322170109057083713 : (((((((p3 ∧ p2) ∨ (p1 ∧ p2)) ∨ (p5 ∨ p4)) → (p4 ∨ False)) → (p2 ∧ False)) ∧ p2) ∨ (((True ∨ (p4 → (False → p5))) ∨ p3) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324174225370668810004655483508 : (p5 ∨ (((p4 ∧ p5) ∧ ((p5 ∨ p4) ∧ ((p1 ∨ p3) ∧ p3))) ∨ ((((False ∧ p2) ∧ p5) → False) ∨ ((p4 ∨ p5) ∨ ((p1 ∧ p4) ∧ False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620321270924258404545175414997 : (((((p1 ∨ p1) ∨ (p4 ∨ (((p3 ∧ (p4 ∨ (False ∧ p2))) ∨ True) ∨ (((((False → p2) → p4) → (p2 ∧ False)) ∨ True) ∨ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_157310577129278364654339533308 : (((p1 ∧ (p2 ∧ ((((p1 ∨ False) ∨ p2) ∨ (True → p2)) → ((p4 → (False → p2)) ∧ p4)))) → False) ∨ ((p2 ∨ (p1 → (True ∧ True))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655066833573691912978014670890 : (((((p4 ∧ (((False → ((p3 ∨ (False → (p2 ∨ (p1 → p1)))) ∧ p4)) → (p2 ∧ ((p5 ∨ p1) → p2))) ∨ p4)) → False) ∨ (False → p1)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_259234554576555860720881130488 : ((False → False) → (p3 ∨ ((p2 → (((((p3 → p1) ∨ False) ∨ ((p2 → p5) ∨ (True → (False → p5)))) ∨ (p1 ∧ p2)) → (p5 ∨ p2))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608053991981703542484754297788 : ((((((((p2 ∧ (False ∨ p1)) ∧ (False ∧ ((p3 ∧ True) ∧ (p4 ∨ (True ∧ (p2 ∨ (p4 → (p5 ∧ p4)))))))) ∧ p5) ∧ p1) ∨ p3) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136590702566345778520397662940 : (((False ∨ (p1 ∧ True)) ∨ ((p5 ∨ False) → ((p2 → True) ∧ ((p2 ∨ ((False ∨ p4) ∧ p3)) ∨ (p4 → (p2 ∨ True)))))) ∨ (p1 ∨ (False ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321849811716586298342866507881 : (p5 ∨ (((p5 → ((p3 ∨ p1) → (p4 → ((((False ∨ p2) ∧ (p5 ∧ False)) ∨ ((p2 ∧ (p4 → (p2 ∧ True))) ∨ p4)) ∨ p2)))) ∨ p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114436003759814947493809670791 : (((p2 ∨ ((False ∨ p5) ∨ (p2 ∧ ((((p2 → (True → (p2 ∨ p5))) ∨ p2) ∧ p4) → p2)))) ∨ (((True ∨ p1) → p5) → p5)) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41614757455288919991417397321 : ((((True → ((p5 ∨ ((p4 ∧ True) ∧ p4)) → False)) ∨ ((((p1 → False) ∨ (True ∧ p1)) ∧ (((p5 ∨ p3) ∧ p1) → p3)) ∨ p2)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135961376695137336730445664865 : (((p4 ∧ (False ∧ ((((p4 ∨ p4) ∧ p1) ∧ p3) → False))) ∧ ((p2 ∧ (((p3 ∨ p1) ∧ p3) → (False ∨ p2))) ∨ True)) ∨ ((p3 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805832347811094066751149544578 : (((p3 → (p5 → (((False ∧ (((True ∧ False) ∧ (True ∧ p3)) ∧ (False ∧ (False ∨ (p2 ∨ p3))))) → ((False ∧ (True ∨ p3)) ∧ True)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116822911598293530284436983656 : (((p4 ∨ p5) ∨ (((((p5 ∧ p4) → (p1 → p5)) → False) ∨ True) ∧ (((p3 → True) ∨ p1) → (((False ∧ p5) → True) ∧ p5)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181406317892982076853073636724 : ((p2 ∨ (((p4 ∨ p1) → ((p3 ∧ ((p5 ∧ p1) ∧ False)) → p5)) → False)) → ((False ∨ p2) ∨ ((p5 → (p2 ∧ ((p4 ∨ p3) ∧ p4))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p4 ∨ p1) → ((p3 ∧ ((p5 ∧ p1) ∧ False)) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h4
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194267986404391508493350144891 : ((p5 → ((p3 ∨ (p4 ∧ (False ∨ (p2 ∨ p5)))) → p4)) → (p2 ∨ ((p3 → p5) ∨ (False → (((((p5 ∧ p1) ∨ False) ∨ p2) ∧ p4) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712841403307020133607256623135 : (((((p1 ∨ False) → ((False ∧ p5) ∨ p5)) ∨ ((p2 ∨ ((True ∨ p1) ∧ (p5 ∧ (False ∨ ((False → p1) → ((p1 ∧ True) → True)))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592986085239346392785292885693 : (((((p3 → (((p2 → (p3 ∧ ((p1 ∧ p2) ∧ p2))) → p1) → (((p1 ∧ (True ∧ True)) ∧ p2) → p4))) ∧ (p5 ∨ (p4 → p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250885696760525114468320311136 : ((p1 → p3) ∨ (((True → p4) ∧ ((((p3 → (True → p4)) ∨ (p1 ∨ (False → ((False → p1) ∨ p5)))) ∧ True) → p2)) → ((p5 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47486342074445692986014989598 : (((False ∨ (((((p3 → False) ∨ (True ∧ (p4 ∧ (p5 ∨ (p1 ∨ p3))))) ∨ p4) → (p1 ∧ (True ∨ False))) ∧ (p4 → p5))) ∨ (p1 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688567824907311140376810953077 : ((((p2 ∨ ((((((((False → False) → p5) → p3) → True) ∨ p4) ∧ False) → False) → p4)) ∧ (((p4 → False) → ((p3 → p1) → p2)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250883457746878444516311124079 : ((p1 → p3) ∨ ((((((True ∨ (p2 ∨ p5)) ∨ p5) ∨ (False ∧ (p5 → (p1 ∧ True)))) → (p2 ∧ (p5 ∨ p1))) ∨ True) ∧ ((False → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114394266781921151660016466904 : (((((((False ∧ ((True ∨ p5) ∨ (p2 ∨ p2))) ∧ p2) → p3) ∨ p3) → ((p1 ∧ p4) → p2)) ∨ (p3 → (False → (p2 ∧ p2)))) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_619462641782415234550846773086 : (((((p2 ∨ (p1 ∨ p4)) → (p3 → ((True ∧ (p2 ∨ (p1 ∧ ((p3 ∧ p2) ∨ p1)))) ∨ ((False ∨ (p3 ∧ (p4 ∨ p3))) ∧ p4)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338052706365713605953352340824 : (p1 → ((True → ((p2 ∨ (p5 ∨ ((p2 ∧ p4) ∨ p4))) ∨ False)) ∨ (((p5 → ((((p4 ∨ p4) ∨ p2) → True) → (p5 ∧ p1))) ∧ p1) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216831605397307954684445428273 : (((p4 ∧ (p2 ∨ p5)) ∧ True) → (((True → False) ∨ (((p5 ∧ True) ∧ False) ∨ ((p1 ∧ (p4 ∨ False)) → ((p4 ∨ p4) → (p2 → p1))))) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h7.left
      let h17 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h21.left
      let h26 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h21.left
      let h31 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157752331941637945438573650030 : (((((p3 → (p3 → (p2 ∧ p1))) ∧ p2) → ((p3 → p5) ∧ p4)) ∧ (False → (True ∧ (p2 → True)))) ∨ (True ∨ ((p4 → p3) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136884481766996042878142331316 : (((p2 ∨ p2) ∨ ((((((True ∧ p3) ∨ ((p3 → p4) ∧ (p1 ∨ p1))) ∧ (p3 ∨ p3)) ∧ p5) → False) ∨ (p5 ∧ p2))) ∨ ((p5 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673502508617041463861378744328 : ((((((False ∨ (False ∧ False)) → p1) → (((p1 ∨ ((p2 ∨ False) → p5)) ∨ ((p1 ∧ (False ∧ p2)) → p1)) ∧ p4)) → ((True ∨ p3) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113123953087211905990787413757 : (((p1 → (((((p2 ∨ ((True ∨ (p5 ∧ True)) ∨ (True → ((p1 ∨ p5) ∨ p3)))) ∨ p3) → True) ∧ p1) ∨ (False → p1))) → p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198451353484766472785070118939 : ((p5 ∧ ((p1 ∨ ((p1 ∨ p4) ∨ p4)) → p2)) ∨ (p3 ∨ (p1 → (((p4 ∧ p2) ∨ p4) → ((True → ((p2 → (p1 ∨ p5)) ∧ p5)) ∨ True))))) := by
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
theorem thm_5_vars_310507955561023962607200203848 : (p2 ∨ ((p1 ∧ (True ∧ ((p3 → p1) → False))) ∨ (True ∨ (((p3 ∧ ((True → (((p1 → (False ∨ True)) ∨ p2) ∨ False)) ∨ p5)) → p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306614179221852794674571005433 : (p1 ∨ ((p3 → p4) → (((((((p5 ∨ (True → (True ∨ False))) ∨ True) → p4) ∧ (p1 ∨ False)) → p3) ∨ ((True ∧ False) ∨ False)) ∨ (False → False)))) := by
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
theorem thm_5_vars_233877589349987643977473240624 : ((p4 ∨ (False ∨ p5)) → (p4 ∨ (p3 ∨ ((((p5 ∨ p5) → p3) → ((((p5 ∨ True) ∨ p5) ∨ p1) → p3)) ∨ ((p4 ∨ p3) ∧ (p1 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h11 : (p5 ∨ p5) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h10
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h12 := h6 h11
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h14 : (p5 ∨ p5) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h15 := h6 h14
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h17 : (p5 ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h18 := h6 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : (p5 ∨ p5) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h20
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686961199779350346895060687468 : ((((p2 ∨ (p2 ∨ ((((((p2 ∨ (p1 ∧ p5)) → (p5 ∧ True)) ∧ p5) → p4) → p1) → p4))) → (p3 → (p4 → (p5 → (False ∨ p4))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157481226733919056639956706966 : ((((((((p4 → p4) ∧ False) → (p3 → p4)) ∧ False) ∨ p2) ∧ ((p3 ∨ p1) ∧ p3)) ∨ (p5 ∧ p1)) ∨ ((p2 ∨ ((True → False) → p2)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_692354950479059116437627994450 : ((((((p4 → (p4 → (p5 ∨ False))) ∧ (((p2 → p1) ∧ False) ∨ p3)) → p5) ∧ (True → (((p3 ∧ p5) → (False → (False → p5))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39015563745962551943279502831 : ((((True → True) ∧ (p2 → (((p3 ∨ p5) ∨ p1) ∧ (((p1 → p5) ∨ (p1 ∨ ((p1 ∨ (p5 → (p4 ∨ True))) → p3))) → False)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314233530756899253560449280633 : (p3 ∨ ((((((p5 ∧ False) ∧ ((((p5 ∨ (p3 ∧ (p2 → p1))) → p2) ∧ p4) ∨ p4)) → (True ∧ True)) ∧ p3) → False) ∨ ((p1 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677384445441796076544995262296 : (((((((((p3 ∧ (p1 → True)) → ((True ∧ p5) ∧ p5)) → ((True ∧ p5) ∧ p3)) ∧ True) ∨ p1) ∨ p5) ∨ ((True ∨ (p2 ∧ False)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2211515244556530254015506763 : (((((p3 ∧ p4) ∨ (p5 → False)) ∧ (p5 → (p4 ∨ ((p2 → True) → True)))) ∨ p5) → ((p1 ∨ p1) ∨ (p3 → (p2 → (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114735508659459935484440794563 : ((((p5 ∧ ((p3 → p2) ∨ False)) ∨ ((True ∨ (True ∨ p3)) → (p3 ∧ (p2 ∧ p2)))) → (((p3 ∨ p2) ∨ (False ∨ p4)) ∧ p2)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321000460857666477837907517698 : (p4 ∨ (False ∨ (((p1 ∧ (p5 ∨ (p1 ∧ (p3 → ((((p5 ∨ (p3 ∨ (p4 ∨ p3))) ∧ p3) → (p5 ∨ p3)) ∧ p2))))) ∨ p4) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2365145443327512294606341541 : (((((False → (p5 ∨ (p4 ∨ (p5 ∨ p1)))) ∨ True) → True) → p4) ∨ ((p3 ∧ ((p5 → p1) ∨ (p4 → (p5 ∧ p5)))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112538465833755697790191117589 : (((((((p5 ∧ ((True → ((p4 ∧ p3) → p1)) ∨ False)) ∨ True) ∨ True) ∨ (p5 ∨ ((p5 ∧ (p2 → p2)) → True))) → p1) → p4) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186206520438312693227411561030 : (((p3 ∨ (p2 ∨ (True ∨ (p1 ∨ ((False ∨ False) → True))))) ∨ False) → (((p1 → (p1 ∨ (p4 → (p2 ∨ (True → (p2 ∧ p4)))))) → p4) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55335250216349778807321970109 : (((p5 ∨ ((p1 ∧ p2) ∨ (p4 ∨ p2))) ∨ ((((True ∧ ((p5 ∨ (True → True)) → (p5 ∧ (p1 → p5)))) → p5) → (p1 ∧ p3)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52316354271965343798878021221 : (((((True ∨ ((p3 ∧ (p4 ∨ ((p3 ∨ p5) → p2))) ∧ False)) → p4) ∨ p1) ∧ ((p4 ∨ ((p1 ∨ p3) ∨ (p1 ∧ False))) ∨ (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181187746074470285760765153483 : ((p1 ∧ (True ∨ (((p4 ∨ (p5 ∧ True)) → p3) → (p1 ∨ (p3 ∨ p5))))) → ((p3 → (((p1 → p4) ∨ ((p4 ∨ p4) ∧ p5)) ∨ p3)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186547623881695412754802810527 : (((((False → p4) ∨ p3) → (p2 ∧ (True → p1))) ∨ (p5 ∨ p2)) → ((False ∧ p3) ∨ (False → (p4 ∨ ((True ∨ ((p4 → p5) → p3)) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258804599236188905360827060490 : ((True → False) → (p4 ∧ ((((True ∨ (p4 ∧ p5)) ∨ p1) → (p1 ∨ ((((True ∨ ((True ∧ True) ∧ (p3 → False))) ∨ p1) → True) ∧ p1))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50653357508796202126212133006 : ((((False ∧ ((p3 ∧ ((p4 → p4) → True)) → (p5 ∧ p3))) → (p3 ∨ (p4 → (p2 ∨ (False ∨ False))))) → ((False ∨ (p3 ∨ p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114198823261175553018159714890 : ((((p4 ∨ (p2 ∨ ((p4 → p2) ∨ (p1 ∨ p3)))) → ((p2 → p5) → ((p4 ∨ (False → p4)) ∧ p3))) → ((p3 → False) ∨ False)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180580208855600199028453746925 : ((((p2 ∨ False) ∨ ((p5 → (p2 ∨ p5)) ∧ p2)) → (p1 ∧ (False ∧ True))) → ((True → (p5 ∨ p2)) ∨ (((p2 ∨ True) ∨ p3) ∨ (p2 → p3)))) := by
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
theorem thm_5_vars_185095558696932552345909793988 : (((p5 ∨ p4) ∨ (((p5 ∧ False) ∧ (False → (True → p1))) ∧ p3)) ∨ ((((True ∧ True) → (((p3 ∧ p5) → (p5 ∨ p3)) → p1)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_883580197081224956659598719243 : ((((((p4 → False) → p1) ∧ ((((False ∨ (p1 ∧ p1)) → p4) ∧ p1) ∧ (p3 → (True ∧ ((p1 → p4) ∧ (True ∧ False)))))) ∨ (False ∧ True)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64505243416186469619831724315 : ((p1 ∨ (((p5 ∨ p4) ∨ (p5 ∧ ((p4 → p2) ∨ ((p5 → p4) ∨ (p2 ∨ p4))))) ∨ ((((p2 ∧ p4) → True) ∧ p5) → (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256807946316989024018728242868 : ((p1 ∨ p2) → (True → ((((True ∨ (((True ∨ False) ∧ (False → False)) ∨ ((p1 ∨ p2) ∧ True))) → (p2 ∨ p1)) → p4) → (p4 ∧ (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ (((True ∨ False) ∧ (False → False)) ∨ ((p1 ∨ p2) ∧ True))) → (p2 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : ((True ∨ (((True ∨ False) ∧ (False → False)) ∨ ((p1 ∨ p2) ∧ True))) → (p2 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h28 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h29 =>
            -- False on the left can always be used.
            apply False.elim h29
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h34 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h35 := h3 h21
    -- One of the premise coincides with the conclusion.
    exact h35
  -- Implications on the right can always be decomposed.
  intro h36
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h37 =>
    -- One of the premise coincides with the conclusion.
    exact h36
  case inr h38 =>
    -- One of the premise coincides with the conclusion.
    exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247421080270141550451115778135 : ((False ∨ p2) ∨ (((p1 → ((False → p3) ∨ True)) ∨ (p2 ∨ (p1 ∧ ((p3 → p2) → ((True → p2) ∧ ((p1 ∧ p2) → p2)))))) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173208816776945457971442020581 : ((p5 ∨ (((p4 → False) ∧ (p4 → (p1 ∨ p1))) ∨ (((p4 → p1) ∨ p5) ∨ False))) ∨ ((True ∨ ((False ∧ p4) ∨ p1)) ∨ (p2 ∧ (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



