variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356065252132679198891736020484 : (p5 → ((((p5 ∨ (p5 → (p5 ∧ (p5 ∧ True)))) → ((True ∨ (True → p4)) → (p1 ∧ (p1 ∧ p3)))) → False) → (p3 → ((False ∨ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720987708121392401587653932848 : (((((p1 → True) ∧ (p4 → p4)) → (((True → False) ∧ (p4 ∧ (((p1 → p5) → False) ∧ True))) → ((p1 ∨ (p3 ∧ (p2 ∧ True))) → p1))) ∨ False) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h2.left
    let h19 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h27 := h18 h26
    -- False on the left can always be used.
    apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685219290332893568727077158878 : ((((True → ((p3 ∧ (p3 ∨ ((p1 → (p4 ∨ (p2 ∨ p5))) ∧ False))) ∧ (p1 → (p3 ∨ p2)))) ∨ ((p2 ∧ (p2 ∧ (p3 ∨ True))) → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_668893497783935044199515686974 : ((((((p2 ∨ True) → (((p3 → p1) ∨ ((((p1 ∨ p3) ∨ True) ∨ p4) ∨ (p1 ∧ p2))) ∧ (p2 ∧ False))) ∨ p5) ∨ (True ∨ (False → p3))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_345528402152772531169513356346 : (p3 → ((((True → ((p2 → p4) ∧ (False ∨ p4))) → (p2 ∧ True)) ∨ (((True ∨ (p3 → p5)) ∨ p2) → ((p3 ∨ (p3 ∧ p2)) ∨ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63435039491937873922193884412 : ((p5 ∧ (p2 → ((((((p1 → p5) ∧ ((True ∨ (True → p4)) → True)) ∧ p2) → p2) → (p2 → (p3 ∧ (p4 ∧ False)))) ∨ (True ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252920939094278576784850781435 : ((True ∧ p1) → (True → (((((((True ∧ p2) ∧ (False ∧ p1)) ∧ p5) ∧ (p3 ∧ ((p5 ∧ (p1 ∧ (p5 ∧ p2))) → p2))) ∨ p4) ∨ True) ∧ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257690482225321547353867506854 : ((p3 ∨ p3) → (((p5 ∨ p2) ∧ ((((p2 ∨ p1) ∧ p1) ∧ p1) → (p3 ∨ (p5 ∧ (p2 ∧ p1))))) ∨ ((p2 ∨ (False ∧ p5)) → (p1 ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225366346606815097883104150628 : (((p2 ∨ True) ∧ p1) ∨ (((True ∧ p5) → (p2 → p4)) ∨ (p4 → ((((p4 → (p3 ∨ p1)) ∧ (p1 ∨ False)) ∨ True) ∨ (p4 ∨ (p2 → p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114007380560053608029312014034 : ((((((p3 ∨ (True ∨ p4)) ∧ (p1 → p1)) → ((p2 → (True → True)) ∧ (p3 → (p1 ∨ p5)))) ∧ p3) ∨ (p2 ∨ (True → True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165820344901761455674210576140 : (((True ∨ (False → p5)) ∧ ((p2 ∨ p1) ∧ (((p1 ∨ True) → (p5 ∨ p5)) → (p1 ∧ p5)))) ∨ (p4 → (True ∨ (((p4 → True) ∧ False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233876193035949174023355044814 : ((p4 ∨ (False ∨ p4)) → (((p4 ∧ p1) ∧ (p3 ∨ ((p1 ∨ ((p4 ∧ p2) ∨ (p5 → (p5 → p1)))) ∨ ((p4 ∨ (False ∧ p5)) ∧ False)))) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679761820698911558093952745762 : (((((((True ∨ (p5 ∨ True)) ∧ (p2 ∨ p4)) ∧ (((False ∨ p3) → p1) → (p1 ∧ (p1 → p1)))) ∨ p1) → (p2 → (False ∨ (p2 → True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322137430260355555351663686662 : (p5 ∨ ((p2 ∨ (((((p1 ∨ p2) ∨ (p5 → p4)) ∨ True) → p5) ∨ (True ∨ ((False → (True ∨ (False ∨ p3))) → (p3 → (True ∧ p3)))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_190545729376936984615139674237 : (((((p2 ∨ (p2 ∨ p1)) ∧ p5) ∨ (p2 → True)) → False) ∨ (p1 → ((p4 ∨ (p5 → (True ∨ p3))) ∧ ((False → False) ∨ ((p2 ∨ p5) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179696438023104407231448915701 : (((((((False ∧ (True → p3)) → p2) ∨ (p4 ∨ p4)) ∨ p2) ∨ False) ∧ p5) → ((p3 ∧ ((False → p5) → p1)) → (((p2 → True) → p2) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : (False → p5) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h12 := h4 h10
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h15 : (False → p5) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- False on the left can always be used.
            apply False.elim h16
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h17 := h4 h15
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h19 : (False → p5) := by
            -- Implications on the right can always be decomposed.
            intro h20
            -- False on the left can always be used.
            apply False.elim h20
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h21 := h4 h19
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h24 =>
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178417179648168826123558062835 : (((p1 ∨ (p2 ∧ (p2 → (((p4 ∧ True) → False) ∧ p5)))) → (p2 ∧ False)) ∨ (p1 ∨ (p1 → ((False ∧ (((p2 → True) ∨ True) ∨ p1)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191449004126320765853365086615 : (((p1 → False) → ((p5 ∨ (False ∨ p2)) ∨ (p4 ∨ p4))) ∨ (p4 ∨ (((p3 ∧ ((p2 ∨ p1) ∧ (p4 → False))) ∧ ((False ∧ p5) ∧ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98824877366124236950308501440 : ((True → ((True ∨ (((p1 ∨ True) → ((p3 ∨ p5) ∧ (p5 → (p2 → ((p4 ∨ (p2 ∧ ((False ∧ True) → p2))) → p2))))) ∧ p2)) ∧ False)) → p1) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737150408616472218978960388017 : ((((p3 → p4) ∧ (False ∧ (((p4 → p5) ∨ (p4 → p1)) → ((p4 → p1) ∧ (p2 → ((p4 → (p1 ∨ ((p3 → True) → p5))) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38094732947801550874704878139 : ((((p4 ∨ ((((p1 → (((True ∨ p2) → p5) ∨ (p4 ∨ ((p3 ∧ p4) → (p5 ∧ True))))) ∧ p4) ∨ False) ∨ p4)) → (p1 ∧ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64060668026171834605706409270 : ((False ∨ (((((p5 → p5) → (p4 → (p4 → p3))) → ((p3 ∨ (True → p3)) ∨ (p3 ∨ p3))) → p5) → (False ∧ (p5 ∨ (p1 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179681688068549263100917594748 : (((((p3 ∨ ((p4 → False) ∧ p5)) ∧ ((False ∨ p2) → p1)) ∧ p2) ∧ True) → ((True ∨ ((True → p2) → p1)) ∧ ((p1 → (p5 ∨ p5)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793628252594414229449273158265 : (((True → (p4 ∨ (((p5 → True) ∧ (p4 ∧ p5)) ∨ ((((((p3 ∨ False) ∧ p5) → p4) ∧ (p1 ∧ p1)) ∨ (p3 ∨ (True ∨ p3))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192466957647906014853996636504 : ((((p1 ∨ (p5 ∧ (p3 → p3))) ∨ (True ∨ p5)) ∨ p4) → (p2 ∨ (((p4 ∨ p3) → (p2 ∧ (p5 → (p1 ∨ (False → (p3 → p1)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159017162248423132920099018473 : ((p4 ∨ ((((((p2 ∨ p5) ∧ p3) → True) → p3) ∧ ((True ∧ p5) ∧ p2)) ∨ ((False → p1) ∧ True))) ∨ ((True ∧ ((p3 ∧ p1) → p2)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_8071002054616579049128230094 : (((((((True → p3) ∧ ((False ∨ True) ∧ (p5 → False))) → True) ∧ (((p2 ∨ (p4 ∨ True)) ∨ (p5 ∨ p1)) → (False ∨ True))) ∨ p2) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214598488241371773141292431931 : (((p4 ∨ p5) ∧ (p5 ∧ False)) ∨ ((p3 ∧ (p4 ∧ ((((True ∧ True) ∧ (p1 → ((p3 → p4) ∨ False))) ∧ (p3 ∨ (p4 ∧ p5))) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240899110577246959589511745265 : ((True → True) ∧ (p2 → ((((p3 → ((p5 → p3) → (p1 → p3))) → ((p3 ∨ (True → (p5 ∨ (p5 ∨ p1)))) ∨ p3)) ∧ p2) ∨ (p2 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384797741774166239806289087379 : ((((((p5 ∧ p4) → (p3 ∨ ((p3 → p3) ∨ (True ∨ (((((p1 ∨ (p2 ∨ (False ∧ False))) ∧ p5) → True) ∨ p2) ∧ p2))))) → p5) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_147814528219806453980457559866 : (((p4 ∧ (p1 ∨ ((True → (((p3 → True) ∧ ((p1 ∧ (True ∧ (p5 ∧ True))) ∧ False)) ∧ p3)) ∨ p3))) → False) ∨ ((p3 → False) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149927230356797466791006615193 : ((p3 ∨ ((((True → p4) → (p4 ∧ (p4 ∧ False))) ∨ (p1 ∧ False)) ∨ ((p2 → (p4 → p1)) → (True ∨ p2)))) ∨ ((True ∨ True) ∧ (p1 ∧ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4265818538718961398256309381 : (True → ((((p2 ∧ ((p4 → (False → True)) ∧ (p2 ∧ (p4 → (p1 ∧ ((p2 ∧ (p3 → p4)) ∨ p2)))))) → (p4 ∨ p3)) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670114712794403152734437422562 : ((((((p1 ∧ (False ∨ (True ∨ p1))) ∧ p2) ∨ (p3 ∧ (False ∨ (((p4 ∨ p3) → (False → p3)) ∧ (p3 → True))))) ∨ (True ∨ (True ∨ p4))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_112115736500222717271781814476 : ((((p4 → False) → ((p1 ∨ ((p1 ∧ (p2 ∨ p2)) → ((p3 ∧ p1) ∧ True))) ∧ (p3 ∨ ((False ∧ (p4 ∨ True)) → p2)))) ∨ False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798962896110157753568931673336 : (((p1 → ((False ∨ p5) ∨ (((((((p1 → (False → p1)) ∧ p1) ∨ p3) ∧ True) ∧ (p4 → False)) → ((p1 ∨ False) → (p5 ∧ True))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89182622959583015678955015763 : ((((False → True) → p4) ∧ (((True → p3) ∧ (((p4 → (p4 ∨ (p1 ∧ ((p4 ∨ (False ∨ p5)) → False)))) → True) ∨ (False → p4))) ∧ p1)) → p4) := by
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231371816542024316877287958249 : (((False → p3) ∨ p1) → ((p2 → (True ∧ (True ∧ (p4 → False)))) ∨ (((True ∧ p4) ∧ (p3 ∧ p2)) ∨ ((True → (p5 → (p2 ∧ p4))) → True)))) := by
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
theorem thm_5_vars_171325786932105597329090474440 : (((((True ∧ p1) ∧ (p5 ∧ ((p4 ∨ (p4 ∧ (p1 ∧ p4))) ∧ p2))) ∨ False) ∧ p1) ∨ (True ∨ (p4 ∨ (p5 → (((p2 ∧ True) → p4) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171882291095387280685499174672 : (((True ∨ ((p2 ∨ p1) ∨ ((False ∧ ((p3 → (p1 ∧ p3)) ∧ p4)) ∨ p5))) → p1) ∨ (p5 → (((p1 ∧ ((False ∨ p2) → False)) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41421028361359758329952372432 : ((((p2 ∨ (False ∨ (((p2 ∨ (((p2 ∧ p5) ∧ p4) ∨ p3)) → True) → p1))) ∨ (p4 ∨ (False → (((False → False) → True) ∧ True)))) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135993527176609988993641888263 : ((((p4 ∨ p3) ∧ (p2 → (False ∧ (p5 → (True → p3))))) ∨ ((((False → p4) ∧ p4) ∨ p5) → (p3 ∨ (p2 ∧ True)))) ∨ (True ∨ (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190047831001162289436349094264 : ((((False ∧ (False ∧ (p1 → (p3 ∨ p5)))) ∨ p3) ∧ True) ∨ ((p1 → p1) → (((False ∧ ((False ∧ (False ∨ (p4 ∨ p1))) ∨ p1)) ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255617468490577382428585190122 : ((p5 ∧ p4) → (((((p2 → (True → (p4 ∨ (p1 ∧ (p4 → True))))) → p5) ∧ (p1 → (p5 ∨ ((True ∨ p2) ∧ p2)))) → False) ∨ (p2 ∨ p4))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651042246746644912580583863358 : (((((((p4 ∨ p2) ∧ p3) ∨ p4) ∧ ((((((p2 ∧ p3) ∧ p5) ∧ p2) ∨ p3) → (p3 → True)) → (p5 ∧ (False → p5)))) ∧ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264201831675505652069888480780 : (True ∧ (((p5 ∨ False) ∨ ((p5 ∨ (p2 → p3)) ∧ True)) → (p3 ∨ (p4 ∨ (p3 ∨ (False → ((((p4 ∧ p2) ∨ p1) ∨ (False ∧ p1)) ∧ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h12
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112322000232835049010553241742 : (((p3 → (((((False ∧ False) → p3) → p3) ∧ p3) → ((True → ((p5 → p1) → ((p4 → p1) ∨ (True → p5)))) ∧ p3))) ∨ p2) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54018913221375306101664954321 : ((((p1 → ((((p4 → p3) → p4) ∨ True) ∨ p5)) → p2) → (True ∧ ((((p3 ∧ p3) → (p2 ∧ True)) ∨ p2) ∧ (False → (p1 → True))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((((p4 → p3) → p4) ∨ True) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350920720111918922400584916671 : (p4 → ((((False ∧ (p1 ∧ p4)) ∨ (((p2 ∨ p3) ∨ (p4 ∨ (p3 → ((((p3 → p2) → False) ∨ False) ∧ p3)))) ∧ p3)) ∨ True) ∨ (True → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147397858869980987643677159612 : (((((True → (False ∧ p5)) ∨ (p1 ∧ True)) ∧ (((((p1 → p1) ∧ p4) ∧ True) ∧ (p1 ∨ p5)) ∨ False)) ∨ True) ∨ (True ∨ ((p1 → True) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164054388329066761108134626879 : ((p1 ∨ ((((p1 ∨ (p2 ∨ (True ∨ (p5 ∧ p1)))) → ((p2 → p1) → p2)) ∧ False) ∨ True)) ∧ (p1 ∨ (((p3 ∨ True) ∧ (p4 → p5)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66051999825354268279936282167 : ((p5 ∨ ((((True ∨ p5) → (p1 ∧ (((p1 ∨ (p1 ∨ (((p2 → p2) → (p1 ∧ (p5 ∧ p3))) ∧ True))) ∧ p5) ∨ True))) ∨ True) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209435840683653442568509440921 : ((p2 → ((p4 ∨ p3) → (p2 → True))) → (p1 ∨ ((((True ∧ (p4 ∧ (False ∧ p4))) ∨ p2) → (p3 ∧ p2)) ∨ ((p4 → p4) ∨ (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258790233720549637077627816349 : ((True → False) → (((False ∧ (False ∨ (p2 ∧ p2))) ∨ p3) ∨ (((p2 → (True ∧ p4)) ∨ (((False → p4) ∨ ((p2 ∧ False) ∨ p1)) ∨ True)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328269774494133735996075983164 : (True → ((((p3 ∨ (((True → True) ∨ (p3 → ((p1 ∨ (p4 → True)) → (p5 ∧ True)))) → False)) ∨ p1) ∧ False) ∨ ((False → False) ∨ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165694683605796729438420497922 : (((False ∨ (p5 ∨ ((p5 ∨ False) ∨ False))) → (False ∨ (((p1 ∨ p3) → (p4 ∨ False)) ∧ p1))) ∨ (p5 ∨ (True ∧ ((True ∧ (p2 → p2)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317694635498514771152754124684 : (p4 ∨ ((((((((p5 ∧ p5) → p4) ∧ p4) ∨ (p2 ∧ (False ∨ p1))) ∨ (((False ∧ False) → p3) ∧ p5)) ∧ (False ∨ p5)) ∧ (p2 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65884291297609740828651305867 : ((p4 ∨ ((p5 ∨ p1) → ((p1 ∨ (((p4 → p5) ∧ (((p2 ∧ p1) → True) ∧ p4)) ∨ p5)) → (p4 → (p5 → (False ∨ (True ∧ True))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_991776095409062010519411899442 : (((p4 ∧ ((False ∨ ((((p4 ∧ (p2 ∨ p1)) ∨ p3) ∨ ((False ∧ (False → p4)) → (p3 → ((p4 ∧ p2) ∨ p2)))) ∧ p4)) → (False ∧ p3))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ ((((p4 ∧ (p2 ∨ p1)) ∨ p3) ∨ ((False ∧ (False → p4)) → (p3 → ((p4 ∧ p2) ∨ p2)))) ∧ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706168450983861826590838035926 : (((((p5 → False) → (p4 → ((p5 ∨ p2) ∧ False))) ∧ ((p3 → (((p4 → ((p2 ∧ p3) ∧ p1)) ∨ (True → (False ∧ p2))) → p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8986833362313864648935868041 : ((((p2 ∧ ((((p3 ∧ p3) → p4) ∨ (True → ((False ∧ (p1 ∧ p3)) ∨ p1))) ∨ p3)) ∨ ((True → ((p2 → p1) ∧ False)) → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164739769332916947252795772354 : ((((p4 ∧ (((True ∧ p1) → p2) → (p1 → (p2 → (p2 ∨ p5))))) ∧ (p1 ∧ p2)) ∨ p1) ∨ (False ∨ ((((p4 ∨ True) → p2) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116354941062556275460915952934 : ((((True → p2) ∨ True) → ((p2 ∨ ((p4 ∨ p2) ∨ (((False → p5) → p4) ∨ (True → (True → ((False ∨ True) ∨ p2)))))) ∨ True)) ∨ (p1 ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198006379882948374733631887208 : (((p1 → False) ∧ ((p2 ∧ (p1 ∨ p3)) ∨ p2)) ∨ (p1 ∨ ((True → (p1 → p1)) ∨ ((False ∨ (True → (((True → p5) → p3) → p3))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47049999690404450598258679465 : ((((p2 ∨ (p3 ∧ ((False ∨ (((True ∧ (True → p4)) ∧ p2) ∧ (p1 → (p3 ∧ (p1 → p4))))) → p3))) ∧ (p4 ∨ p5)) ∨ (True ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117020645544194280105478732267 : (((p1 ∨ p5) → ((p1 → ((False ∨ p4) ∨ ((p4 ∧ (((((p5 ∨ p3) ∨ p4) → (p4 → False)) ∧ p3) ∧ False)) ∧ p1))) ∧ p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135868106724885136144844075199 : (((((True ∧ p1) ∧ ((p1 ∨ p3) → p3)) ∧ (p1 ∨ (p2 ∧ p5))) ∨ (((((p5 ∨ p3) ∨ p2) ∨ p3) ∧ False) → p1)) ∨ ((p3 → True) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h3
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257136047951185754465517323627 : ((p2 ∨ p1) → (((((((p5 ∧ p3) → ((p5 → p1) ∧ p5)) → p1) → p2) ∨ p2) ∧ (p2 ∧ ((True ∧ (p4 ∨ p4)) ∧ False))) ∨ (p1 → True))) := by
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
theorem thm_5_vars_878805785761969801763680487667 : ((((p3 ∧ ((((((p2 ∨ (p4 ∧ p3)) ∧ (False → (p3 → p4))) → False) ∨ ((p5 → p4) ∨ p5)) ∧ p4) → (p3 ∧ False))) ∧ (p3 ∧ p4)) → p1) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (((((p2 ∨ (p4 ∧ p3)) ∧ (False → (p3 → p4))) → False) ∨ ((p5 → p4) ∨ p5)) ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38897516655655219490398648878 : (((((p3 → p5) → p4) ∨ (((p2 ∧ p2) → ((((p1 → ((p1 ∨ p3) → (p1 ∨ p3))) ∧ p5) → (p3 ∧ True)) ∧ p3)) → p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52536907345082923668478742424 : ((((p5 ∧ (((p1 ∨ (p5 ∧ p3)) ∨ p2) → ((p1 ∨ False) ∨ p2))) ∨ p4) ∨ (True ∨ ((p5 ∧ p4) → ((p2 ∨ p4) ∨ (p1 ∨ p1))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789231906012130468655557984187 : (((p5 ∨ (((((False → (False ∨ (p2 → (p5 → (((p1 ∨ False) → p3) ∨ p5))))) → p3) → p2) ∨ p1) ∨ ((p4 ∧ p2) ∨ (p3 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141030970458602659264754694514 : ((((p4 → p4) ∧ (p1 ∧ ((False → False) → p4))) ∧ (p1 → ((((p5 ∨ (p2 ∨ p5)) → p1) ∨ p5) ∨ (p3 ∨ p3)))) → (p2 ∨ (p4 ∨ p2))) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_501534980037380488996101410308 : ((((p4 ∨ (p1 ∨ False)) ∨ (True → (((p2 ∧ (p1 ∨ p5)) ∨ (((p5 → True) ∧ True) ∧ (p1 ∧ (p1 ∨ p1)))) → (p1 ∨ (p4 ∨ p5))))) ∧ True) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51974645824233884082994580413 : ((((True → (False → p3)) → ((p1 ∧ (((p1 → True) → p4) ∨ p2)) ∧ (p4 → False))) ∨ (p4 ∨ (True ∨ (p3 ∧ (True → (False → True)))))) ∨ p5) := by
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
theorem thm_5_vars_674079072462322984662200010687 : ((((p2 ∧ ((((p2 ∨ ((False ∨ (p2 → p3)) → ((p5 ∧ (True → p1)) ∨ p4))) ∧ (p1 ∨ p5)) ∨ p4) → p1)) → (p1 → (p3 → p3))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760325255365149159527164373708 : (((p2 ∧ ((True ∧ p3) → (True → (p4 ∧ (((p1 ∨ p2) ∨ (p1 ∨ (p1 ∧ p3))) ∨ ((((True ∧ p5) ∧ p4) → (False ∧ True)) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493427024423064961512942785 : ((((p1 ∨ ((p2 ∨ ((p1 ∧ ((False ∨ (False ∧ (True ∨ p3))) ∧ p5)) ∨ p1)) ∧ (True ∧ (p4 ∨ (p1 ∨ True))))) ∨ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204874602169647228721788322423 : ((((p1 ∨ (p3 ∨ p5)) → p4) → p3) ∨ ((p3 ∧ ((p3 ∧ (p2 ∨ (((p5 ∨ ((p4 ∨ p1) ∨ (p1 ∧ p2))) → p4) → p4))) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651027603297949081323575090054 : (((((True → (False → (p3 ∨ (p4 ∨ False)))) → (((((p1 ∨ (False ∧ p2)) → ((True → p1) ∧ True)) → True) → p1) ∨ p5)) ∧ (p4 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224316466842888833267501632153 : ((False → (p1 ∨ p3)) ∧ ((p5 → (False ∨ p4)) ∨ (p4 → ((p5 ∨ (True ∨ True)) ∧ ((p5 ∨ ((True → (p5 ∨ p2)) ∨ p1)) ∨ (p1 ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650353389355826032407517605472 : (((((p1 → (((p2 → (p1 ∨ p5)) → False) ∨ ((p1 ∨ p3) ∨ (p5 ∧ p1)))) ∧ (((p2 ∧ False) ∧ p3) ∧ (p5 ∧ p5))) ∧ (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2503801175881382925774430845 : ((True → ((((p3 → p1) → p2) → (True → True)) ∧ p4)) → (((True ∨ True) → (p4 ∨ (((p5 → False) ∧ p1) ∨ (p4 ∧ p4)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17858129516312338223000368772 : (((((p1 ∧ p5) ∧ ((((p3 ∨ True) ∧ p3) → ((p2 → (p5 ∧ True)) → p5)) ∧ (p1 ∧ False))) ∨ False) ∨ ((True ∧ (False → p1)) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704967019132257465003205820104 : ((((True → ((p2 ∨ p4) ∧ (((False ∨ p5) → p5) ∨ p2))) → (p5 ∧ (p2 → (p3 ∧ (((((False ∨ p1) ∨ p3) ∧ p3) → p5) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218196944734298503589261452375 : (((p2 ∧ p1) ∨ (p1 → p3)) → ((((p3 → (False ∧ (p2 ∨ p5))) ∧ p5) ∨ ((p1 → p5) → True)) ∨ ((((p5 → p5) ∨ p1) ∧ True) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198911739241185027870623690047 : ((p3 → (True ∧ (((p2 ∨ p4) ∨ p1) → p4))) ∨ ((p2 ∨ p4) → ((p2 ∧ p3) → ((p5 ∧ p3) ∨ ((False ∨ (True ∧ (False → p5))) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337390871589942195308544681482 : (p1 → ((False ∨ (((False ∧ (p5 ∧ p4)) ∨ (((((((p3 → p1) ∨ p5) → p4) ∨ False) ∨ p3) ∧ p5) → True)) → p5)) ∨ ((p5 ∧ p3) → p5))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321561792395771678488894403903 : (p4 ∨ (p2 → ((p5 ∨ (p5 → ((p3 → True) → p2))) ∧ ((p4 ∨ ((True ∨ True) ∧ (p2 → (((True → p2) → p3) ∧ (p4 ∧ p5))))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h16 := h8 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185200983437431619589292202252 : ((True ∧ ((p2 ∧ (p4 ∧ False)) ∧ ((p4 ∨ False) ∨ (p1 ∨ True)))) ∨ ((p1 → True) ∨ ((True → ((p1 ∧ (p2 ∧ p4)) ∨ p1)) ∨ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44675187940289449106768809598 : ((((((True → p1) → p2) ∧ (p2 ∨ p4)) → ((((p5 ∨ (True → p1)) ∨ (p1 → (p4 ∨ p1))) ∨ (p5 ∧ False)) → (p4 ∨ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96474505799466287794799193285 : ((False ∨ (((p4 ∨ (p4 → (p2 ∨ True))) → p1) ∧ (p4 → (((p3 → (p3 ∧ (False ∨ p2))) ∧ False) ∨ (p5 ∧ (p4 ∨ (p5 ∨ p4))))))) → p1) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ (p4 → (p2 ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311231731448812182054475075892 : (p2 ∨ ((p2 → p4) → (((((True → p2) → p3) ∨ p3) ∨ ((p5 ∨ (p1 → p3)) ∨ p2)) ∨ (((False → (False ∧ (True ∨ True))) ∨ p5) ∨ True)))) := by
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
theorem thm_5_vars_686266826971639987891110739110 : ((((((p4 ∨ ((p4 → False) ∨ p4)) ∧ (True ∨ p4)) ∨ (((p1 → p1) ∧ (False ∨ p4)) ∨ p3)) → ((p1 ∧ True) → ((p4 ∨ p2) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719023183798496586823414159804 : (((((p3 → p4) → (p1 → False)) ∨ (True ∧ (((p3 ∨ (((p5 ∧ p2) → (True ∧ (p3 ∨ p4))) → ((p4 ∧ p2) ∧ True))) → p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204500266866252936325819836225 : ((((p5 ∧ (True ∧ p2)) ∨ False) ∨ p3) ∨ ((((p1 ∧ (((p2 ∨ True) ∧ True) ∨ p3)) → True) ∧ ((p4 ∨ True) ∨ True)) ∨ (p4 ∨ (True → True)))) := by
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
theorem thm_5_vars_115008608730154746911906514223 : ((((True ∨ False) ∧ (((p5 ∧ p3) ∨ (p3 ∨ (p4 → p4))) ∨ p5)) ∧ (p1 ∨ (p2 → (p2 ∧ (((p3 ∨ p2) ∨ p2) ∧ p2))))) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346289639875008309190927403593 : (p3 → (((p4 ∨ (((((True ∧ True) ∨ p2) ∨ (p2 → ((p5 → p5) → p1))) ∧ True) → (((p2 → True) → p2) ∧ p4))) ∧ p1) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215429593556984387063470911413 : ((p3 ∧ ((p5 ∧ p2) ∨ False)) ∨ (p1 → (p4 → ((((True ∨ p3) → p1) ∨ p3) → ((True → (False ∨ True)) ∨ ((True ∧ (True ∨ p5)) ∧ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111160713893067023190619193503 : ((((p2 → ((p5 ∨ p3) ∧ (p5 ∨ False))) → (((True ∧ (p3 → p5)) ∧ ((True ∧ p4) → p4)) → (p4 → (p5 ∧ p2)))) ∧ p4) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



