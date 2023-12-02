variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42185817492650072315008629988 : (((True ∧ ((((False → (p5 ∨ ((p1 ∧ p5) ∧ False))) → (p3 ∧ p5)) ∧ ((p3 ∨ (p1 ∧ p4)) ∧ True)) ∨ (True ∨ (p4 → p4)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213194427949350523498141822531 : ((((p5 ∨ p2) ∨ p3) ∧ True) ∨ ((p1 ∨ p2) → ((p1 ∧ True) → ((p2 → p2) ∧ (True → (p4 ∨ (((p4 ∨ (p1 ∧ p4)) → p4) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442796510250646319299812953428 : ((((((p5 ∨ (p1 ∧ (True ∧ (((p4 → p1) → (True → False)) ∨ False)))) ∨ ((p3 ∨ p4) ∧ True)) ∧ (p2 → False)) ∨ ((True ∧ p5) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_41923026805246008878948335015 : ((((p4 ∧ (p4 ∧ True)) → (p1 → (p2 ∨ (((p5 ∧ (p2 ∨ ((True ∨ (p2 ∨ p4)) ∧ (False ∧ p5)))) ∨ p4) ∨ (p1 → True))))) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138054702546038197304286030951 : ((True → (True ∧ ((p5 ∨ p2) ∨ (((((p4 ∧ True) → (True ∨ p5)) ∨ p5) → (p5 ∨ p2)) ∨ ((p3 ∧ True) ∧ True))))) ∨ ((p3 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64357910835856862356255875527 : ((p1 ∨ (((((p5 ∧ p3) ∨ ((p3 → p5) ∧ (p5 → p2))) → (p1 ∧ (p5 ∧ (((True ∨ p3) ∧ p1) → p5)))) ∨ (p1 ∨ True)) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_780504486235404678421856428267 : (((p2 ∨ ((p1 → (False ∨ ((True ∨ (((False ∧ p2) ∧ (p1 ∨ p1)) ∧ p3)) ∧ p5))) → ((p4 → (((p5 ∨ p1) ∨ True) ∧ p3)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214699454457584694090150723637 : (((False ∧ True) ∨ (False ∨ p4)) ∨ (False ∨ ((p4 ∨ (p1 ∧ False)) → ((False ∨ ((True → p4) ∨ p1)) → (p3 ∨ (False → (p5 → (p5 ∨ p4)))))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h7
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84141761559477919416686909186 : (((p2 ∧ (p4 ∨ ((True → ((False ∧ p4) ∨ ((p5 ∨ p2) ∧ p4))) ∧ (True ∨ False)))) ∧ (p4 → (p3 ∧ (p4 ∨ ((True ∧ p1) → p5))))) → p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h18
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299285725565518924715146036016 : (False ∨ (((((((p2 → False) → p1) ∨ p3) ∨ (False → True)) ∨ (p2 → p5)) ∧ (p2 → (p1 → (((True ∧ False) ∨ (p3 ∨ p1)) ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696052598745463786461616166724 : ((((p3 ∧ ((False ∨ ((True ∨ p3) ∨ True)) ∧ ((True ∧ (False → p2)) → True))) → (((p1 ∨ p5) → p4) ∨ ((p5 ∧ (p1 ∨ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46217156075642826971592954807 : (((((((True ∨ p2) ∨ p1) → p4) → ((p2 ∨ p5) ∧ (((((False ∧ p1) → p1) ∨ p2) ∨ p2) ∧ p1))) ∧ (p2 ∧ False)) ∧ (p4 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38754055262980084187497577541 : (((((False ∧ p2) ∨ (p4 ∨ False)) ∧ (((((p1 ∨ p5) ∨ p3) ∨ True) → ((p4 → (((p5 → p2) ∨ p1) ∨ True)) → p5)) ∨ False)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46909743325261343128050953038 : ((((((False ∨ (p3 ∧ (p2 ∨ ((p4 → p5) → (p4 ∨ True))))) ∧ (p4 → True)) ∨ ((p3 ∨ True) ∨ (p2 ∨ False))) ∨ True) ∨ (p3 → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126004930788074867817618038728 : (((False → True) → ((False ∨ ((p1 ∨ p5) → ((p5 ∨ (((p4 ∧ p2) ∨ (False ∧ False)) → (p4 → p5))) → p4))) ∧ (False ∧ p3))) → (p5 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336136765347241597958167431555 : (p1 → (((p5 ∧ (p5 ∧ ((((p1 → (p3 → p2)) ∨ ((((p5 ∨ p2) ∨ p4) ∨ p2) → p1)) ∨ p4) → ((p3 ∧ p5) ∧ False)))) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59055265391509733421178362014 : (((p4 ∧ p4) ∨ (((p1 ∧ p2) → True) → ((((p2 → ((p2 → (False → (p5 ∨ False))) ∧ False)) ∨ False) ∧ p4) ∧ ((p5 ∧ p3) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246135215728259301365243696437 : ((p4 ∧ p2) ∨ ((p1 ∨ (((p5 ∧ (True → (True → p2))) → p4) ∧ (((((p2 ∧ p2) ∧ True) → p4) ∧ (p3 → (False ∨ False))) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672086645556318403639382751037 : ((((((False → (p3 → (True ∧ (p5 ∨ p1)))) → (p3 → (p3 ∧ (((p2 ∧ (p1 ∧ False)) ∨ p1) ∧ p1)))) ∨ p3) → ((p1 ∧ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148596164034841649080204206614 : (((True ∧ ((p5 → (p1 ∨ ((True → p3) ∨ False))) ∨ p3)) ∨ ((((p3 ∧ (p2 ∨ p3)) → False) ∨ p3) ∨ p4)) ∨ ((p2 ∧ (p1 ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118386993368853547553300850644 : ((p2 ∨ (((p4 ∨ (p3 → p3)) ∨ ((p1 ∨ p4) ∧ p5)) → ((p2 ∧ p5) → (False ∨ ((True ∧ False) ∨ ((True ∧ False) → p5)))))) ∨ (p3 ∨ p4)) := by
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
  cases h1
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
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
theorem thm_5_vars_260937591551120754273431711036 : ((p4 → False) → (True → ((p4 → (((False ∨ True) → p2) → (False ∨ (p4 ∧ (((p5 ∧ p5) ∧ True) ∧ p2))))) ∨ ((p5 → p4) ∨ (p2 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245407254302212364308373902310 : ((p2 ∧ p4) ∨ ((p5 → (((((((p4 ∨ p1) ∨ p1) → p4) ∧ ((True ∨ (True ∧ p5)) ∨ p5)) ∧ p5) ∨ (p2 ∨ (p3 → p5))) ∨ p3)) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612578333055835494193159647732 : (((((((p1 ∧ p5) → (p1 ∨ ((p4 → ((False ∧ ((True ∧ (True → p3)) → p1)) → p4)) ∧ (p5 ∨ p5)))) → p1) ∨ (p4 → p4)) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_693212190657859718598656038366 : ((((p1 ∨ ((((((p1 → p1) ∧ p1) → False) ∧ True) → (p1 ∨ p4)) → p4)) ∧ ((True ∧ False) → (False → (False → ((True ∨ p5) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153257472259266817499676880611 : ((False ∨ ((p4 ∨ (p5 ∨ ((p5 → (p2 ∧ ((True → True) ∨ True))) ∨ False))) ∨ ((p5 ∨ (p1 → p2)) ∧ p5))) → ((True → (p5 ∧ p4)) ∨ True)) := by
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
            -- False on the left can always be used.
            apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133787752315562243022661679981 : ((((p5 ∧ (p2 ∨ p5)) ∧ ((True → (((False ∨ p1) → (p4 ∨ True)) ∨ (True ∨ p1))) ∧ (p2 → (p5 ∨ p1)))) ∧ False) ∨ (p5 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200680269754582521119781908233 : ((p1 ∧ (p3 → (p1 → ((p1 ∨ p5) ∨ p4)))) → (((((False ∨ ((p1 ∨ False) ∨ (p4 → p4))) → p5) → p2) ∨ p1) ∧ (p4 → (p5 ∨ p1)))) := by
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736255199379535032760391555279 : ((((False → p2) ∧ (p5 → (p2 ∨ (((False ∨ (p5 ∧ ((True ∧ ((p1 ∧ p2) ∨ ((p3 ∨ p3) ∨ True))) ∧ False))) ∧ (p3 ∨ True)) ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
theorem thm_5_vars_157016347687607351821458933821 : ((((p2 → (False ∨ p1)) → ((p2 ∧ ((p4 → p4) → ((p5 → (p3 → p5)) ∧ p4))) ∧ p5)) ∨ False) ∨ (((p3 ∨ (True → p4)) → True) ∧ True)) := by
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
theorem thm_5_vars_328959649478164007027836826852 : (True → (((p2 ∧ p4) → ((p3 ∨ p2) → True)) ∧ ((((p4 ∧ p2) ∨ ((p4 ∨ True) ∧ p3)) ∧ p4) ∨ (True ∧ ((True ∨ (False ∨ p3)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151555967782162669047705029532 : (((((p5 → p2) → (((p5 → (p3 ∧ p1)) → ((False ∨ True) → p1)) → (p4 → p4))) ∨ p5) → (p1 ∧ p3)) → ((p2 ∧ p3) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p2) → (((p5 → (p3 ∧ p1)) → ((False ∨ True) → p1)) → (p4 → p4))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253784835133670617957655569915 : ((p1 ∧ p2) → (((p2 ∧ (((p1 ∨ (False ∨ p5)) → ((((False ∧ p2) ∧ p2) → p3) ∨ p4)) ∧ True)) → (p3 ∧ ((p2 ∧ False) ∧ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635019492030993303215336034295 : ((((((p3 → ((True → (p5 → p1)) → ((p3 → ((p4 → p5) ∧ True)) ∧ ((p1 ∨ p5) → p5)))) ∨ p3) → ((p3 ∧ p4) → p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249245208188690122079734571319 : ((p4 ∨ p4) ∨ ((p2 ∧ (p1 ∨ (((((p5 ∨ p2) → p1) → p3) ∨ ((p4 ∧ p3) ∧ ((p2 ∨ p5) ∨ False))) ∨ True))) ∨ ((p3 ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658373916943133206114178494783 : ((((False ∨ ((((p3 → (False ∧ p4)) ∨ p3) → ((p4 ∧ ((p2 ∨ (p1 ∧ True)) ∧ p1)) ∨ p2)) ∧ ((p5 ∨ p1) ∨ p5))) ∨ (True ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49667724147014918758314582599 : (((((p3 ∧ p3) ∨ False) → ((p3 → (p4 ∨ p5)) ∧ ((p5 ∧ (((True ∧ p3) ∧ p1) ∨ (True ∨ False))) ∧ False))) → ((p5 ∧ p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734372902302511631809321228333 : ((((False ∨ p4) ∧ ((p5 ∨ (p2 ∨ ((((True ∨ ((p2 ∧ p4) → p4)) ∨ (((p4 → p4) ∨ p1) ∧ (True ∧ p2))) → p5) ∧ True))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316701230246089636795778670314 : (p3 ∨ (p5 ∨ ((False ∨ (p2 ∨ p3)) → ((p3 ∨ (((p5 ∨ (p4 ∨ p3)) ∨ p2) ∨ ((False → (False → (p5 → (p2 → p4)))) ∧ p1))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111873204406731629237161642940 : ((((p1 ∨ (((p2 → p1) → (p3 ∨ (((True → (p3 ∧ p5)) ∨ False) ∨ p3))) ∧ False)) ∨ (((p2 ∧ p5) ∧ p2) ∨ p3)) ∨ True) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205279166379966330133116779830 : (((True ∧ (False ∧ p3)) ∨ (p1 ∨ p2)) ∨ ((False ∨ ((((p4 ∨ (p5 → p2)) ∧ (p1 → True)) → (((p1 ∨ p2) ∧ p1) ∨ p4)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659986298108544905297269037407 : ((((((False → (True ∧ (False ∨ (((False ∨ p3) ∨ ((True → False) ∧ (p3 → p2))) → ((p2 → p1) → p4))))) ∨ p5) ∨ p2) → (p1 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65762162536646313501250851623 : ((p4 ∨ (((((False → p1) ∧ (p4 ∧ p4)) → (p1 ∧ p4)) ∨ (p1 ∨ ((True ∨ True) ∧ (True → p2)))) → (p1 ∨ (p4 → (p4 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303042447891217847233829100620 : (False ∨ (p2 → (((((p1 ∧ (p4 ∨ (((p1 ∨ (True ∧ False)) ∧ p3) ∨ (p1 ∧ ((p1 → p2) ∧ p2))))) ∨ True) ∨ (p1 → False)) ∨ p3) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_321245102743225539436312021896 : (p4 ∨ (p4 ∨ (((p2 ∧ ((p4 ∧ ((((p2 → (False ∧ p4)) ∨ False) → (p1 ∧ p5)) → ((p1 → p1) ∧ p2))) ∧ True)) → False) → (p5 → p5)))) := by
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
theorem thm_5_vars_810637534819813226049988515667 : (((p5 → (((True → True) ∨ p4) ∧ (((p4 ∧ (False ∧ (p4 ∨ ((((p4 → p1) → p1) ∨ p3) ∧ p4)))) ∧ (True ∧ (p1 → p2))) ∨ p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160145089054243914976335675993 : ((((p5 ∨ (p2 → (p1 ∨ (p2 ∨ (p2 ∧ (False ∧ (p1 ∨ (p2 ∧ p3)))))))) → p3) ∧ (p3 → p5)) → (p1 ∨ (p3 ∧ ((p1 → p5) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p2 → (p1 ∨ (p2 ∨ (p2 ∧ (False ∧ (p1 ∨ (p2 ∧ p3)))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135454765593749206392940895553 : ((((p3 → ((((p5 ∨ p3) ∨ (((p3 → p1) ∧ p1) ∧ p3)) → p2) ∧ (p5 ∧ p1))) ∨ p1) → (p1 ∨ (p2 ∨ p3))) ∨ (p3 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189038065473658204213520176238 : (((p2 → (False ∨ False)) ∨ ((False → p5) ∨ (p2 ∧ p3))) ∧ (p5 ∨ ((p1 ∧ (p4 ∧ p4)) ∨ (((p4 ∨ (False → (p2 ∧ p4))) → p3) → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ (False → (p2 ∧ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69099836957743834088058499791 : ((p5 → ((p5 → (((p2 ∧ True) ∨ (((False → p5) ∨ (False ∨ (((p2 ∨ True) ∨ (p1 ∨ (p2 ∨ p4))) ∨ p5))) ∧ True)) → p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627889862890662283147092131254 : ((((((((p4 ∧ True) → ((p4 ∧ (p2 ∨ p3)) → p1)) ∨ p2) ∧ ((True ∨ p2) ∨ ((True ∨ (p2 → (p3 ∧ p5))) ∨ False))) ∧ p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115014006890700282870788207996 : ((((p5 → p1) → ((p3 ∨ ((False → p1) → (p4 ∨ False))) ∧ False)) ∧ (p5 ∧ (p4 → ((p5 → ((p2 ∨ p4) ∨ p3)) ∨ p1)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114120274018776837109743448031 : (((True → ((p3 → (p5 → True)) → (True ∧ (p2 ∧ (False ∧ (p5 ∨ (p1 ∨ ((p4 ∨ p3) ∨ True)))))))) ∨ (p1 ∧ (False → p1))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214519874030809792424583142828 : (((p4 ∧ p4) ∧ (True ∨ p3)) ∨ (((p3 ∨ (p2 ∧ (p4 ∨ (True ∨ p2)))) ∨ ((((p1 ∧ p5) ∨ p1) → True) → True)) ∨ ((p1 ∧ p4) ∨ p1))) := by
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
theorem thm_5_vars_586463547446705446804454365659 : (((((((p1 ∧ p5) ∧ p5) ∨ (((p4 ∨ p5) ∨ ((p1 → ((p2 ∧ (p3 → p5)) ∧ p5)) ∨ p2)) ∧ ((p4 → True) ∧ p2))) ∧ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150154614306950685555212037369 : ((p1 → ((p4 ∧ ((True ∧ ((True ∨ (p1 ∧ p4)) → (p3 ∨ p1))) → ((p4 → p2) ∧ False))) ∨ (p2 ∨ p1))) ∨ ((p5 → True) ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192692924339005628244961738943 : ((((p1 ∧ ((p3 ∨ True) → p2)) ∨ (p1 → p1)) → p3) → ((True → (p3 → (((p3 ∧ True) → (True → p4)) ∧ (p1 → (p1 → p1))))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∧ ((p3 ∨ True) → p2)) ∨ (p1 → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738172628707441888138438466927 : ((((False ∧ p2) ∨ ((p5 ∨ p4) → (((p2 ∨ p3) ∧ p2) ∨ ((p4 → ((True → ((True → p2) ∨ ((p5 → False) → p2))) ∨ p3)) → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106191421951680440209675529670 : (((((((p5 ∨ True) → p3) ∧ p3) ∨ (False → p1)) ∨ (p2 → False)) → (p2 ∨ ((p2 → p2) → (((p5 → True) ∧ p3) → p3)))) ∧ (False → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152043360993110419245283901349 : (((p5 ∨ (p4 ∧ (p3 ∨ (False ∨ (p2 ∨ (True → False)))))) ∧ (True ∧ (((p5 ∨ p5) → p4) → (True ∨ p5)))) → ((p5 ∨ (False ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h3.left
          let h18 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h3.left
          let h21 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328091350987534359602957885444 : (True → (((((True → ((p5 ∨ p4) ∧ ((((p5 ∧ p5) → p2) ∧ p2) ∧ ((p3 ∧ p2) → True)))) → p3) → p4) ∧ p1) ∨ (True ∨ (p3 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639042255312467129113921398307 : ((((((True → (p2 ∨ p5)) ∧ p1) ∨ ((((p4 ∨ ((p5 → True) ∧ p5)) ∧ True) → (True → (p1 ∨ ((p4 → False) ∨ p2)))) → True)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714423985889493861880638518093 : (((((p2 ∧ (p2 ∨ False)) → (p4 ∧ p4)) → (True → (((p2 → False) ∧ (((True ∧ (True ∧ (False ∧ p3))) → p2) → p1)) ∨ (False → p2)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60253665124233388725338161391 : (((False → False) → (p1 ∧ (((((True → ((p1 → p3) → p5)) → ((p3 ∧ (False ∨ p2)) → (p3 ∧ p4))) ∧ p5) → p3) → (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78369069415588143524489924702 : (((((((p3 ∨ (p4 → (p4 → p4))) ∨ (p1 → True)) ∨ (True ∨ p3)) ∧ ((p2 → (False → (p1 ∧ p5))) → p4)) ∧ p1) ∧ (p3 ∨ p2)) → p4) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h11 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h12 : (p2 → (False → (p1 ∧ p5))) := by
            -- Implications on the right can always be decomposed.
            intro h13
            -- Implications on the right can always be decomposed.
            intro h14
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h14
            -- False on the left can always be used.
            apply False.elim h14
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h15 := h7 h12
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h17 : (p2 → (False → (p1 ∧ p5))) := by
            -- Implications on the right can always be decomposed.
            intro h18
            -- Implications on the right can always be decomposed.
            intro h19
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h19
            -- False on the left can always be used.
            apply False.elim h19
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h20 := h7 h17
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h22 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h23 : (p2 → (False → (p1 ∧ p5))) := by
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h25
            -- False on the left can always be used.
            apply False.elim h25
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h26 := h7 h23
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h28 : (p2 → (False → (p1 ∧ p5))) := by
            -- Implications on the right can always be decomposed.
            intro h29
            -- Implications on the right can always be decomposed.
            intro h30
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- False on the left can always be used.
            apply False.elim h30
            -- False on the left can always be used.
            apply False.elim h30
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h31 := h7 h28
          -- One of the premise coincides with the conclusion.
          exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h33 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h34 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h35
          -- Implications on the right can always be decomposed.
          intro h36
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h36
          -- False on the left can always be used.
          apply False.elim h36
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h37 := h7 h34
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h39 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h40
          -- Implications on the right can always be decomposed.
          intro h41
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h41
          -- False on the left can always be used.
          apply False.elim h41
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h42 := h7 h39
        -- One of the premise coincides with the conclusion.
        exact h42
  case inr h43 =>
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h45 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h46 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h48
          -- False on the left can always be used.
          apply False.elim h48
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h49 := h7 h46
        -- One of the premise coincides with the conclusion.
        exact h49
      case inr h50 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h51 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h52
          -- Implications on the right can always be decomposed.
          intro h53
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h53
          -- False on the left can always be used.
          apply False.elim h53
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h54 := h7 h51
        -- One of the premise coincides with the conclusion.
        exact h54
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h56 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h57 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h58
          -- Implications on the right can always be decomposed.
          intro h59
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h59
          -- False on the left can always be used.
          apply False.elim h59
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h60 := h7 h57
        -- One of the premise coincides with the conclusion.
        exact h60
      case inr h61 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h62 : (p2 → (False → (p1 ∧ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h63
          -- Implications on the right can always be decomposed.
          intro h64
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h64
          -- False on the left can always be used.
          apply False.elim h64
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h65 := h7 h62
        -- One of the premise coincides with the conclusion.
        exact h65



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_879293039381262607629239243462 : ((((p2 ∨ ((p4 ∨ p5) ∧ ((((p2 ∧ p2) ∨ True) → p2) ∧ (((p1 → p1) ∧ (p2 ∨ (p4 → p3))) → (True ∨ False))))) ∧ (p1 → p2)) → p2) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : ((p2 ∧ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h7.left
      let h15 := h7.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : ((p2 ∧ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247560007107755585170283649839 : ((False ∨ p4) ∨ (((p5 → p5) ∧ p3) → (((((True ∧ (((p3 → p1) ∧ (p3 ∨ p3)) ∨ p5)) → p5) ∨ (p3 ∨ True)) ∧ (True → p4)) ∨ True))) := by
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
theorem thm_5_vars_311890067168122184353151629943 : (p2 ∨ (p2 ∨ ((p3 ∨ (((p4 ∧ p3) ∨ p2) ∨ (p1 ∨ p3))) → (p2 → ((p4 ∨ (((False ∨ p4) ∧ (False → False)) ∧ p2)) ∨ (p2 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112275570205299652671650703835 : (((True → ((p5 ∨ (((p4 ∧ ((((p2 → p4) → (p1 ∨ p1)) ∨ (p2 ∨ p5)) ∨ False)) ∧ p4) ∨ True)) ∨ (p5 ∧ p3))) ∨ p4) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_191323860860033173740869579941 : (((p1 ∧ p2) ∨ ((True ∧ p4) ∨ ((p4 ∨ p1) ∨ p2))) ∨ (((p5 ∧ p5) ∧ (((p3 ∨ p5) ∨ (((p4 → False) ∨ p2) → True)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178569559994072204283364234946 : ((((p4 → True) → ((p3 ∧ p2) → p5)) ∧ ((p5 ∨ (False ∧ p4)) ∨ p1)) ∨ (((p3 → p5) → p5) → ((p5 → (p5 → (p4 ∨ True))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172613808955586145545730371961 : (((p4 → (p3 ∧ p2)) → (p3 → ((True ∧ (p2 ∨ p2)) → (p2 → (p2 ∨ p1))))) ∨ (False ∨ ((p3 ∧ ((False → p2) ∨ True)) ∧ (p4 ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116993841887210722968993383106 : (((True ∨ p2) → (((True ∧ p2) → (True → (((p5 → p3) → ((p2 ∨ p4) → (p3 ∨ (p2 ∧ (False → True))))) ∨ p3))) ∧ p5)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628188945159511168787164714211 : ((((((p2 ∧ True) ∧ (((p1 ∨ (p4 ∨ False)) → (((False ∨ True) ∨ (p4 → ((p4 ∧ p4) → True))) ∨ p4)) ∨ (False ∨ p2))) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55394505002392307460362205832 : ((((p3 ∨ (p3 → (p5 ∧ p5))) ∧ p4) → (((p5 ∨ (((p5 ∧ (False ∧ False)) ∧ False) ∧ False)) ∧ (p3 ∨ p4)) ∧ ((p4 ∨ p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346424356953364263010645178383 : (p3 → ((((p3 → (((((p2 → p1) ∧ ((True ∨ (True ∧ p5)) ∨ p5)) ∨ p1) → p2) ∧ p3)) ∨ (False → (False ∨ p4))) → p2) → (p2 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → (((((p2 → p1) ∧ ((True ∨ (True ∧ p5)) ∨ p5)) ∨ p1) → p2) ∧ p3)) ∨ (False → (False ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326301716789490473221348028025 : (p5 ∨ (p4 → ((((p3 ∧ p3) → True) ∨ (((p3 ∨ (p5 → False)) ∨ (p1 → False)) ∧ p4)) → ((False ∨ p4) ∨ (((p3 ∧ p1) ∨ p3) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64534454707993600336040615287 : ((p1 ∨ ((((False → p1) → ((p4 ∧ True) ∨ p2)) ∨ p4) → ((False ∧ (p3 ∨ p1)) ∧ (True ∧ (p5 → ((p5 → (p1 ∨ p2)) ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233792264212262245288600576772 : ((p3 ∨ (True → p4)) → ((p4 ∧ True) ∨ (p4 → (p5 ∨ (((((p1 ∧ p5) → (p1 ∧ ((p4 ∧ p5) ∨ p2))) → (True → p5)) ∨ p3) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194679413640365972147332039992 : ((((p2 ∨ (False ∧ p5)) → (p3 ∧ p5)) ∨ True) ∧ (((((p4 ∨ p2) ∧ False) ∨ p1) ∧ (p2 ∧ (p4 → (p2 ∨ (p1 ∧ True))))) ∨ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721172559017895817035833828338 : (((((p5 → p2) ∨ (p5 → p3)) → (p1 ∧ (((p2 → ((p5 → p1) ∧ ((p3 ∧ p1) ∨ (p2 ∨ (False ∨ p2))))) ∨ (p3 ∧ False)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209239810461363758067150824847 : ((p5 ∨ ((True → (True ∧ p1)) → p2)) → ((((p4 ∧ p4) → p2) ∨ ((((True ∧ (True → (p5 → False))) → (p5 ∧ p1)) ∨ p2) ∨ True)) ∧ True)) := by
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
theorem thm_5_vars_129072489572370695045732366784 : ((((((p4 ∧ True) ∧ (p1 → (p2 ∧ ((p2 ∧ ((True ∨ (p2 ∨ p5)) → p2)) ∨ p5)))) → (p5 ∨ False)) ∨ p3) ∨ True) ∧ (p5 ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329693268354470014533499029174 : (True → ((p4 ∨ p1) → (((p1 ∨ (p1 ∧ (((p1 → (True ∧ p1)) → p3) ∧ False))) ∧ ((((p1 ∧ True) ∧ p2) ∧ p4) ∧ p1)) ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588524469161943048664321741055 : ((((((p1 ∨ p4) ∨ (p3 → (((((p3 → (p5 ∨ p1)) ∧ (p2 → (False ∧ False))) ∧ p3) ∨ (p4 ∧ (p1 ∨ p5))) ∨ True))) ∨ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732658338820014804980963467308 : ((((p1 ∧ p2) ∧ ((False ∧ (False ∧ p4)) ∨ (p1 ∧ (((((p5 ∧ p2) ∧ ((p2 ∨ p2) → p1)) ∧ p5) → (p2 ∨ (p5 → p5))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149163614856715480783562215338 : (((p3 ∨ p4) ∧ (((p4 ∧ p5) ∨ True) ∨ ((((((p2 → True) ∨ p4) → p4) ∨ p3) ∨ p2) → (p4 ∧ False)))) ∨ (((p4 ∧ p2) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757947953386998724159040863912 : (((p1 ∧ (p5 ∨ (((((((((False ∧ p2) ∨ p5) ∧ p5) ∧ False) ∧ (p3 → (False ∧ (p5 ∨ p1)))) → p5) → p2) ∨ p4) ∨ (p2 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9195949124520954875254431879 : ((((((p2 ∨ p5) ∧ ((True ∨ True) ∧ (p3 → p1))) → p2) → ((p1 ∨ (p4 ∨ (p4 ∧ p2))) ∨ (((True ∧ False) → p4) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215458278946393071063349773886 : ((p3 ∧ (p5 ∧ (True ∨ p5))) ∨ (((p3 ∨ (p3 ∧ (p3 ∧ (p2 ∧ p4)))) ∨ ((False ∨ False) → (p1 ∧ (((p4 ∨ True) → p4) ∨ True)))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46089079346147600292024295139 : (((((((p4 → ((p1 → p5) → False)) ∨ p1) → p3) ∧ ((p5 ∧ False) ∨ ((p3 ∧ ((p3 ∨ p2) → p3)) → p2))) ∨ True) ∧ (p1 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_797411758082655146300983849239 : (((p1 → ((True ∧ ((p4 ∧ p1) ∧ (p4 ∧ ((((True → (p5 ∨ False)) ∧ (p2 ∧ False)) ∧ (p5 → (p3 → p1))) ∧ (p2 ∧ False))))) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158113817067493752602793645927 : (((False ∧ (p3 ∨ (p4 ∨ p1))) ∧ ((((p3 ∨ True) ∨ p4) ∧ (p5 → (True ∨ (p5 ∨ True)))) ∧ p5)) ∨ ((p1 ∧ ((p2 ∧ p5) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191880721636138807408594122243 : ((p4 ∨ (p5 ∧ (((p4 ∨ p1) → False) ∧ (p5 ∨ p5)))) ∨ (((p2 ∧ p4) ∧ (((False → (True ∨ p5)) → False) ∨ ((p4 → p3) ∨ False))) → p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137934646273837823478690686061 : ((p4 ∨ (True → ((((((False → p4) → (p2 → p4)) → p3) → ((True ∧ p3) → p4)) ∧ p1) ∨ (p3 → (p3 → p3))))) ∨ (False → (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256884534763823057213412527921 : ((p1 ∨ p4) → ((p3 ∨ (True ∧ (p1 ∨ ((((p3 ∨ p5) ∨ (p1 ∨ p1)) ∨ (p3 ∨ p5)) ∧ (True → (((p2 → p4) → p1) ∧ p4)))))) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148231774872845523191775262229 : ((((p5 ∨ ((p4 ∧ p4) → ((p2 ∨ p2) ∧ (((p1 ∨ p4) → False) ∧ p3)))) → p2) ∨ (True ∨ (p4 ∨ p4))) ∨ (p1 ∧ ((p4 ∨ p2) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64521000613982071118803887554 : ((p1 ∨ ((p1 ∨ (p2 ∧ (False ∧ ((p4 ∨ True) ∧ (p3 ∧ True))))) ∧ (p3 ∨ (p3 ∧ ((p5 ∨ (p5 ∨ (p3 ∧ (True ∧ p4)))) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_889238989311585282511086292102 : (((((p1 ∧ (p2 ∨ (p4 → p3))) ∨ ((p4 ∧ ((p2 → False) ∨ p1)) ∨ ((((True ∨ (p5 → p2)) ∧ p4) ∨ True) ∧ True))) → (True → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p2 ∨ (p4 → p3))) ∨ ((p4 ∧ ((p2 → False) ∨ p1)) ∨ ((((True ∨ (p5 → p2)) ∧ p4) ∨ True) ∧ True))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137388644791874658762971694835 : ((p3 ∧ ((p5 ∨ p4) ∧ (((((False ∧ p4) → p3) → (p1 ∧ (p2 → True))) → ((p3 ∨ p5) ∨ (False ∧ p3))) ∧ p5))) ∨ (p2 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



