variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80381208556060687826663509317 : (((((p4 ∨ ((False ∨ p1) → False)) ∧ ((False ∧ (p3 → p4)) ∨ False)) ∨ ((False ∨ (((p2 ∨ False) ∧ True) ∧ p1)) → True)) → (p3 ∧ p5)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ ((False ∨ p1) → False)) ∧ ((False ∧ (p3 → p4)) ∨ False)) ∨ ((False ∨ (((p2 ∨ False) ∧ True) ∧ p1)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153424325120763555615256166574 : ((p4 ∨ ((((((p4 → True) ∧ (True ∨ ((p2 ∧ ((p3 ∧ p3) → p5)) → p2))) → p1) → p4) ∨ False) ∧ p3)) → ((p1 ∨ (False ∧ p4)) → p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : (((p4 → True) ∧ (True ∨ ((p2 ∧ ((p3 ∧ p3) → p5)) → p2))) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h14 =>
            -- One of the premise coincides with the conclusion.
            exact h3
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h9
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643434952979406577966592748566 : ((((p4 ∧ (((p1 ∨ (False → False)) → ((p2 ∧ ((True ∧ (((p1 ∨ ((p4 → p5) → p1)) ∨ p4) ∨ p3)) ∧ False)) ∨ p3)) → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337348646956936557729877864422 : (p1 → ((((((p3 → p5) ∨ ((True → p5) ∨ (((p3 ∧ p2) ∧ (p5 ∧ (p2 ∨ p5))) ∧ p3))) ∨ p3) ∧ p1) → p3) ∨ ((p1 → p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151796387649433563281480354317 : (((((((p1 → (p2 ∨ (p1 → True))) ∧ (False → p5)) ∨ p4) ∧ p1) ∧ p4) ∧ ((p2 ∨ (p4 ∧ p3)) ∧ p2)) → (p5 ∨ (p1 → (True ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
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
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66286704788341530458915186545 : ((p5 ∨ ((p4 ∨ True) ∧ (p3 ∧ ((p1 ∧ p5) ∧ ((p1 → (((True ∧ ((p3 ∧ True) → p3)) → True) ∧ (p3 ∨ p2))) ∨ (p3 ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68845329245893552455559026951 : ((p4 → ((p5 ∧ p1) ∨ ((p3 → (((True → p1) ∧ ((((p5 → (p5 ∨ p2)) ∨ (p4 ∨ (p1 ∨ False))) ∧ p5) ∨ p1)) ∨ True)) ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147878405364697463789117051460 : (((p5 → ((p5 → (True → (p1 → ((p5 ∧ (((p3 ∧ (p3 ∨ True)) ∨ p1) ∨ p4)) → False)))) ∨ p4)) → p1) ∨ (((False ∧ False) ∧ p1) → p3)) := by
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
theorem thm_5_vars_204932384405221529523947143740 : ((((p1 ∧ False) → (p3 ∨ p5)) → p3) ∨ (((p1 ∧ False) ∨ ((((False ∧ (p1 ∧ p3)) → ((p1 → p1) → True)) ∨ (p3 → p4)) → p5)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((False ∧ (p1 ∧ p3)) → ((p1 → p1) → True)) ∨ (p3 → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325780830777210200141559599828 : (p5 ∨ (p2 ∨ (p5 ∨ ((p1 ∨ (((p5 → ((p1 ∨ p2) → p5)) → True) → (((p3 → (p3 ∨ p5)) → (p1 ∧ False)) → False))) ∨ (p1 → p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → (p3 ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662595196361370141288317784410 : (((((p1 ∨ ((p5 ∧ False) ∨ (True → False))) → ((p4 ∧ True) → (((p1 ∨ p1) ∨ (p5 ∨ (p4 ∧ True))) ∨ (True ∨ p1)))) → (p2 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683814007803777175340058198162 : (((((((p1 ∧ (p3 ∨ (p1 → (p5 ∨ True)))) ∨ p3) → (((True ∧ True) ∨ False) ∧ p3)) ∨ False) ∨ (p3 ∨ ((p5 ∧ p1) → (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156602681238726349385708382236 : (((((((p4 ∧ p2) ∧ p3) → ((p4 → p2) ∧ True)) ∧ ((p3 ∨ False) ∧ (p4 ∧ p1))) ∧ p3) ∧ True) ∨ (False → (False ∨ (True ∨ (p4 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670717871950930997422923429295 : ((((True ∧ ((((((p1 → p2) ∧ ((p2 ∧ False) ∨ False)) ∨ p3) ∧ p1) ∧ p5) ∨ ((p4 → False) → (p3 ∨ p1)))) ∨ ((False → p2) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132869476229023867363416462671 : ((p3 ∨ (((p4 ∨ (((p5 ∧ p2) ∨ ((p3 → (False → ((p1 → p1) ∨ False))) → p4)) ∧ True)) ∨ p4) ∨ (False → False))) ∧ (p3 → (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147442253481839177867174037601 : ((((p3 → False) ∧ (((((True → p3) ∨ p1) → p1) ∧ (((p5 ∨ (False ∧ True)) → p1) ∧ p4)) ∧ p4)) ∨ p3) ∨ ((True ∧ (True ∨ p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756095320288260735690661897815 : (((p1 ∧ ((p4 → (((p1 → (p3 ∨ (p2 ∨ (((p5 ∧ (p3 ∧ p4)) ∧ ((p2 ∧ p5) → p1)) ∧ p5)))) ∨ p4) ∨ (p5 ∧ p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171398962400027412560430437608 : (((((p4 ∧ p4) ∨ (p4 ∧ False)) ∧ (p2 ∧ (p4 → ((p2 → p5) ∧ p3)))) ∧ True) ∨ ((p2 ∧ ((p4 → ((p2 ∨ p3) ∧ p3)) → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150240559383216896881204766167 : ((p3 → ((False ∨ (p2 ∧ ((False ∧ (p1 ∨ ((((False → p5) ∨ True) ∧ (p5 ∧ p4)) ∧ p1))) ∧ True))) ∨ p5)) ∨ (((p1 ∧ False) → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166836319252481853401700245266 : ((((p1 ∨ (p1 → ((False ∧ p1) → ((p4 ∧ p1) ∨ (p3 ∨ (p5 ∨ p3)))))) ∨ p2) ∧ p3) → (p3 ∧ (False ∨ ((False ∨ False) ∨ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215235992678579366715577987848 : ((False ∧ ((False → p3) ∨ True)) ∨ (((True → (p3 ∨ (p5 ∨ (p4 ∧ p2)))) → (p3 ∧ p4)) ∨ (((p2 → (p1 → p2)) ∧ (False ∨ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214581846945826161816127322372 : (((p3 ∨ p1) ∧ (False → False)) ∨ (((True ∧ p3) → ((False → (p1 ∧ ((p4 ∧ p4) ∧ p2))) → p1)) ∨ (False ∨ ((p1 ∧ (p2 → p2)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_949205464798206057627786635447 : (((((p1 → p4) ∧ p3) ∧ (((p4 ∧ ((p2 → ((False ∨ (p2 → p1)) ∧ (p5 ∧ (False ∨ p3)))) → p2)) ∨ (True ∨ p2)) → (p4 ∨ p4))) → p4) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∧ ((p2 → ((False ∨ (p2 → p1)) ∧ (p5 ∧ (False ∨ p3)))) → p2)) ∨ (True ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165601622931549218106283042823 : ((((p5 ∨ ((p4 ∨ p1) ∧ p1)) ∨ (p5 → False)) → (((p2 ∨ p4) → p1) ∨ (p5 ∧ p4))) ∨ ((p3 → (p4 ∨ ((False ∧ p1) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39102129727757214075790169379 : ((((p1 → p3) ∨ (p5 ∨ (((False → False) → (p4 ∨ (p1 ∧ (True → (((p2 → (p1 ∨ p1)) ∧ p1) → p3))))) ∨ (True ∨ p3)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773587210797156151468065261380 : (((False ∨ (((p1 → p1) ∧ (((((p1 → p4) ∧ p4) ∨ p3) → ((False ∧ (p2 ∧ False)) ∨ (False ∨ p5))) → (p1 ∧ (p2 → p1)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139485822277545741491162744638 : (((((p4 ∧ (((True → (p2 → p5)) ∧ (p3 ∧ (True → p3))) → (p2 → (False → (p3 ∨ p4))))) ∧ True) → p5) → p4) → (p5 → (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ (((True → (p2 → p5)) ∧ (p3 ∧ (True → p3))) → (p2 → (False → (p3 ∨ p4))))) ∧ True) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56504689682209971191286438365 : (((p2 ∧ (True → (p2 → True))) → (((True ∧ (p4 ∨ ((((p4 → True) → p1) → p1) → False))) ∨ p5) ∧ (True ∧ ((p2 → p3) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138245739285415551740998366606 : ((p2 → ((p4 ∧ (False → p1)) ∨ (((p3 ∧ (p2 ∨ p2)) → p5) ∧ ((p4 → ((p3 → p1) ∧ (False ∨ p1))) → p4)))) ∨ (p4 → (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148625915945328069389813184077 : ((((False ∧ p5) → (p5 ∨ ((True → True) → (p3 ∧ False)))) → (((False ∨ p1) ∨ ((p1 ∧ p5) → p5)) → p5)) ∨ ((p4 ∨ p4) → (True → p4))) := by
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
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695117208942210990521368342833 : ((((((p1 ∧ ((((p3 → p1) ∨ True) ∧ (p5 ∧ p3)) ∨ p4)) → p3) ∨ False) → ((False ∧ ((True → p4) → (False ∧ False))) ∧ (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178756012739315982714126611697 : ((((False ∧ p5) ∨ p3) ∧ (p5 ∨ ((p5 ∧ (p3 ∧ (p3 ∧ True))) ∧ p1))) ∨ (((p1 → True) → ((p4 → (p4 ∧ p1)) → (p2 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751068309942299070181619342659 : (((True ∧ ((p1 ∧ (p1 ∨ (p1 → True))) ∨ ((p5 ∧ (p1 ∧ (((((True ∧ (p5 ∧ (True → False))) ∨ p1) → p4) ∧ p4) ∧ False))) ∨ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247833352394663204854646618055 : ((p1 ∨ p2) ∨ ((((((p5 → p4) ∧ (((p5 ∨ p5) ∨ p5) ∧ (False ∧ p4))) ∨ p4) → p1) ∧ (((p1 ∧ p1) ∨ p4) ∧ (True ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198425200435988197733839827181 : ((p4 ∧ ((False → p3) → (True ∨ (p3 → False)))) ∨ (((p3 → False) ∨ (((p1 ∨ p4) ∨ p2) → (False ∨ True))) ∨ (p1 → ((p5 → False) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_264323975461248137726740983211 : (True ∧ ((p1 → (p3 → ((p1 ∧ p5) → True))) → (p5 → ((p2 → (((p1 → (p4 → False)) ∧ False) ∨ p3)) ∨ (((False → p1) ∧ False) ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250156249096276508546440565686 : ((True → p5) ∨ ((p3 ∨ (False ∧ (False ∨ (((p5 → (p2 ∨ p1)) ∨ (False → (p3 → (p4 ∧ (p3 → p1))))) → p2)))) ∨ ((p4 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_572308566760173013254009904518 : (((p1 → ((p5 ∧ (p4 ∧ p2)) → (((((p2 ∧ (p4 ∨ ((p3 → p1) ∧ p2))) ∨ (True → p1)) ∨ ((p3 ∧ False) ∧ p1)) → False) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89169254921636195532244100097 : ((((p3 ∨ p2) → False) ∧ (p2 ∧ (((p3 ∧ p2) ∨ (p4 ∨ (p4 ∧ (True → ((False ∨ p5) ∨ ((False → p4) ∧ (p3 → p3))))))) → True))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137375248021097723293303382834 : ((p3 ∧ ((p2 ∧ ((p3 ∧ False) ∧ (False ∨ (False ∧ (p3 → (p4 ∨ True)))))) ∧ ((p3 ∧ p5) ∨ (p1 → (p4 → False))))) ∨ ((False → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177447749582504143746206765310 : ((True → (p2 → (p1 → ((p1 → ((p5 ∧ (p5 ∧ False)) → p3)) → True)))) ∧ (((((False ∨ (p1 ∨ False)) ∧ (p2 → False)) ∨ p3) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327870770300832495358071505890 : (True → (((True ∨ p4) → (p3 → (((((p1 ∨ (p2 ∨ (True ∧ (True → (p5 ∧ p1))))) ∧ False) ∨ (p5 ∧ True)) ∨ p3) ∨ False))) ∨ (p3 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346329668058205206359130818243 : (p3 → ((((p5 ∨ (False ∧ p2)) ∧ (((p5 → (True ∨ (p5 ∧ (p5 → p4)))) ∧ False) ∨ p4)) ∨ ((False ∨ (p3 ∧ True)) ∧ True)) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598909361154123897915076547340 : (((((True ∨ p4) ∧ ((p5 → (p2 ∨ (True ∧ p3))) ∧ ((p5 → (p4 → (((True → (p1 → (p3 ∨ False))) ∨ p1) ∨ p4))) ∨ p4))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197701945465902346192856844951 : (((p1 → ((p5 ∧ p3) → p5)) → (p2 ∧ p4)) ∨ ((((True ∧ p5) ∨ (True ∨ p4)) ∨ p4) ∨ (p1 ∨ (p1 ∨ ((p3 ∨ (p1 → True)) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246339948396832096699335392428 : ((p4 ∧ p5) ∨ ((p1 ∨ (((p2 → (p5 ∧ True)) ∨ p2) → p5)) → ((p1 → ((p2 ∧ p4) ∧ False)) ∨ (p2 → (((p1 ∨ True) ∨ p5) → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244675183733538072408591808951 : ((p1 ∧ True) ∨ ((((True → False) ∧ (((True ∨ p5) ∨ p4) ∨ (((True ∨ ((True ∨ p3) → False)) ∨ p4) ∧ p2))) → (p5 ∧ (p3 → p4))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h21
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h25 := h2 h24
      -- False on the left can always be used.
      apply False.elim h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h33 := h27 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h35 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h36 := h27 h35
        -- False on the left can always be used.
        apply False.elim h36
    case inr h37 =>
      -- One of the premise coincides with the conclusion.
      exact h37
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h43 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h44 := h27 h43
        -- False on the left can always be used.
        apply False.elim h44
      case inr h45 =>
        -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
        have h46 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h27, we can now drive its conclusion.
        let h47 := h27 h46
        -- False on the left can always be used.
        apply False.elim h47
    case inr h48 =>
      -- One of the premise coincides with the conclusion.
      exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754432774386267270637226882285 : (((False ∧ ((p1 → p4) → (((False → (True → p1)) → ((True ∨ (p2 ∨ (True ∧ p3))) ∧ ((p5 ∧ p5) ∧ p4))) ∨ (p5 → (p4 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197719520093890195221948939786 : ((((False → p4) ∧ p2) ∧ ((p5 → p5) ∨ p1)) ∨ (((True ∨ ((False ∨ True) ∨ False)) → False) → (((p2 ∨ p2) ∧ p3) ∧ ((False ∧ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((False ∨ True) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((False ∨ True) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ ((False ∨ True) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358114787857001075255488898379 : (p5 → (p2 ∨ ((p5 → (((((p2 → True) → ((False ∨ p2) ∨ p2)) ∨ True) ∧ (p3 ∧ False)) ∨ p3)) ∨ (p5 ∨ (p4 ∧ ((True ∨ False) ∨ p5)))))) := by
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
theorem thm_5_vars_623063509691748889854688482262 : ((((p5 ∧ (True → ((((p5 → ((False ∨ p2) ∧ p1)) ∧ p4) ∧ ((((False ∨ p2) ∨ (p3 ∧ False)) → False) ∧ p1)) ∨ (True ∧ p2)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617096333692064164952466082098 : (((((False ∨ (((False ∨ p1) → p4) → (p3 ∨ p2))) ∧ (((p3 ∨ p1) ∨ p5) ∧ (p1 ∨ ((p4 ∧ (p2 → p2)) ∧ (p2 ∧ False))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2083477569724178817308359026 : (((((True ∧ p4) ∨ (((p5 → False) ∨ p4) ∧ p3)) ∧ p5) ∨ (((p1 ∨ p2) ∧ False) → p2)) ∨ ((((True ∧ True) ∨ p3) ∧ p3) ∧ p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308739884271167439725806557575 : (p2 ∨ ((p3 → (p4 ∧ ((p5 ∨ (True ∧ ((p4 ∧ (p1 ∧ (True → (True ∨ ((p1 → (p2 ∨ False)) ∧ (p1 ∨ p3)))))) ∨ p2))) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166592693598079970832249277765 : ((True → (p2 ∧ (p2 ∧ (((p1 ∨ p3) ∨ ((p3 ∨ p3) → (p4 → (p3 → True)))) → p5)))) ∨ (((True ∨ True) ∨ (p2 ∧ False)) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165366114255741216678473179018 : ((((False ∨ (False ∧ ((p4 ∧ (p3 ∧ p1)) ∨ (p3 ∨ p3)))) ∧ p5) ∨ ((p3 → True) → True)) ∨ ((((p2 → p2) ∨ (p2 → True)) ∧ True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609282316542332623443478060346 : ((((((True ∧ p5) ∧ ((False ∧ p3) ∨ ((False ∨ ((p1 → ((p4 ∨ p5) → (p3 ∨ p1))) → p1)) ∨ ((True ∨ p3) → False)))) ∨ True) ∨ p1) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_159358378124230312670106287214 : ((((p4 ∧ ((p1 → (p1 ∧ ((False ∧ p1) ∧ (p2 ∧ (p2 ∨ False))))) → (False ∧ p5))) ∧ p2) ∧ True) → ((p3 ∧ ((False ∨ p5) ∨ p5)) → p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56610752186423205620228013383 : (((p5 → (False → (p4 → True))) → ((((((p3 ∧ ((p4 → (True ∨ p1)) ∨ p2)) → p5) ∨ p5) → True) ∨ (p5 ∨ (p1 ∨ p4))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50962852936369318554784917197 : ((((((p5 → True) ∧ True) ∧ True) ∧ (p5 ∨ (((p3 ∨ p3) → True) ∨ ((True → p5) → True)))) ∧ ((((p3 ∨ False) ∧ True) ∧ p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745420929876529780149546669952 : ((((p5 ∧ p4) → (p2 ∨ (((((p1 ∧ p1) ∧ ((p3 → p4) ∨ p1)) ∨ (p4 ∧ (p4 ∨ True))) ∧ (((p1 → p4) → p5) → p2)) → p2))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 → p4) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h13
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : ((p1 → p4) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h19 := h6 h17
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h24 : ((p1 → p4) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h26 := h6 h24
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h28 : ((p1 → p4) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h30 := h6 h28
      -- One of the premise coincides with the conclusion.
      exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53202766574285673184653206918 : (((((p3 → ((p5 ∧ (p5 ∨ p5)) → p5)) → p1) → (p2 → p3)) ∨ ((p5 → (True ∧ p3)) → ((True → (p1 ∧ False)) ∨ (p4 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730710982316563310871315913735 : ((((p3 ∧ (False → p3)) → (True → (((((p3 ∨ ((p5 → True) → p3)) ∧ p4) ∨ (p2 ∧ (p5 → (p3 → p5)))) ∨ (p2 → False)) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770108019555654396124466438886 : (((p5 ∧ (p4 → (False ∨ (p4 → (p5 → (((False → p1) ∧ ((((p2 ∧ (p5 ∧ p1)) ∧ p3) ∧ (p4 ∧ False)) ∨ (False ∨ p4))) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782373559437930192091764513311 : (((p3 ∨ (((((p2 ∨ p5) ∧ p3) ∨ (((p2 → False) ∨ p3) → (p2 ∨ (True ∧ (p3 ∧ (p5 ∨ (p4 ∧ (p4 → p3)))))))) ∨ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305040510557061284306540396687 : (p1 ∨ ((p5 → ((((True → p3) ∧ p3) → p5) → (((((True ∨ p3) → False) ∨ p2) → (True → (p2 ∨ p2))) → p2))) ∨ ((p4 ∨ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2815430809348082018603192481 : (((p1 → (p4 ∧ True)) ∧ p4) → (p5 → (p4 ∧ (((p3 ∨ (p3 ∨ p2)) ∨ (((p1 ∧ p1) ∨ (True ∨ p3)) ∧ (p5 ∨ p2))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768265395330928899159805417928 : (((p5 ∧ (((p3 ∨ p4) ∨ (((((p2 ∨ p3) → p4) → p3) → p1) ∧ (p3 ∧ (p1 ∨ (p2 ∨ (p3 ∨ p3)))))) ∧ (p5 ∨ (p2 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179579448954462234305445833246 : ((p2 → (p1 ∨ (((((p5 ∨ p5) → (p3 ∧ p1)) → p5) ∨ p3) ∧ p1))) ∨ ((False ∨ True) ∨ (True ∧ ((False ∨ p1) ∧ (p1 ∨ (p1 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336275423794000013964712488788 : (p1 → ((((((((False ∧ False) ∨ p2) ∧ (False ∨ p5)) ∨ p3) → False) ∨ p1) → ((((True → p3) ∨ (p3 ∨ (p2 → True))) → p1) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38628611235067843375787905308 : ((((((True → (p4 ∨ p3)) → p1) → (p2 ∧ p4)) ∨ (True ∧ (((True → p1) ∨ p1) ∧ (False ∨ (((p3 ∧ p2) ∨ p3) → False))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303877452764106825773817133339 : (p1 ∨ (((p3 ∧ (p2 ∧ ((p4 ∨ False) → (p1 ∧ ((p4 ∨ p1) → ((False ∧ (False → p2)) → True)))))) ∧ (((p4 → p2) ∨ p1) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165696184959385820572742116907 : (((p4 ∨ (((p4 → p5) → False) ∧ True)) → ((True → False) ∧ ((False ∧ p2) ∧ (p2 ∧ False)))) ∨ (p3 → ((True ∧ (p3 ∨ p3)) ∨ (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653341031473432623664789847828 : ((((p3 → (((((p5 ∨ (False ∨ (p2 ∨ (False ∧ p1)))) ∧ p3) → (p5 ∧ True)) → (False ∨ (p2 ∧ (p2 ∨ p1)))) ∨ p2)) ∧ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111572926217766283366381819116 : (((((p5 ∨ p4) ∧ ((True ∧ (p2 ∧ False)) ∧ ((False ∨ (p5 ∨ p5)) → ((True ∨ ((True ∨ p5) ∨ p3)) ∧ p2)))) ∧ False) ∨ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64767204859379090064978271528 : ((p2 ∨ ((True → (p2 ∨ (((((p2 ∧ p3) ∧ ((True ∨ p5) ∧ (True → p1))) ∧ False) → False) ∧ ((p2 ∧ p1) ∧ (p3 ∧ p4))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171522503104315114579536744280 : ((((p3 → (((False ∨ (True → (p4 ∧ p4))) ∧ p3) ∨ (True ∧ p5))) ∧ p1) ∨ p2) ∨ (p2 → (((p5 ∨ True) ∨ (True ∨ (p5 ∨ p1))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_135851958989076697032215063450 : (((((((p3 ∧ (p1 → p1)) ∧ (False → False)) → p1) ∨ p1) ∧ False) ∨ (p1 ∨ ((p5 ∧ False) → (True → (p2 ∨ p2))))) ∨ (True ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110742623112270002304033558822 : ((((((p5 ∧ p3) ∧ p5) ∨ (True ∨ ((p5 → p5) → (((p3 → False) → (p2 → p3)) ∨ (p1 → (True ∨ p5)))))) ∧ False) ∧ p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392842358175372711268133215528 : ((((((True → p4) → p5) → (p4 → ((False ∨ (True ∧ ((p4 ∧ ((False → p2) ∧ p1)) ∧ (True ∧ p3)))) ∨ ((p1 → p2) ∧ p1)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_720690967967904504208196993217 : ((((((p1 ∨ p5) → p1) → p4) → ((((((((p3 ∧ p4) ∨ (p1 → (p1 → p4))) ∨ p4) → p3) ∨ p4) ∨ p1) ∧ False) ∧ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1785563842332386154327730004 : (((((p3 → p4) ∨ p3) ∨ (((p3 ∧ p1) ∨ p1) ∧ (p3 → (p4 ∨ p5)))) ∨ ((p1 → (False ∨ p3)) → p4)) ∨ ((False → p5) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174501454040921331807697536077 : ((((p4 → ((p5 ∧ p2) ∧ p2)) → p3) ∨ (p4 ∨ (True → (p2 ∧ (p5 ∧ False))))) → ((p3 → (p5 ∧ ((p3 ∧ p3) ∨ (False ∧ True)))) ∨ True)) := by
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
theorem thm_5_vars_215944843145938735449262206022 : ((p4 ∨ ((False ∧ False) ∧ p2)) ∨ (p5 → (((True → p4) → p3) ∨ ((((p2 ∨ p3) → p2) ∧ (((p2 → p5) → (p2 → p5)) → p3)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 → p5) → (p2 → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152004633264394075784103066911 : ((((False ∧ p5) → (True → ((False → p5) → ((p4 ∨ True) ∨ p1)))) → (((p3 ∨ (p2 ∧ p4)) → p4) ∧ p1)) → (p1 ∧ ((p2 ∧ p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p5) → (True → ((False → p5) → ((p4 ∨ True) ∨ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164597289705571445745371367254 : ((((p1 ∨ p2) → ((p5 ∧ (False → p2)) → ((p4 ∧ ((p2 ∧ p3) ∨ p4)) ∨ p4))) ∧ p5) ∨ (p3 → (p2 ∨ ((p3 ∨ (p3 → p1)) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113450691169675310949017621390 : ((((p5 → (p4 → (p3 ∨ ((True ∧ (False ∨ ((True → p1) ∧ p3))) ∨ (((p3 ∨ p2) ∨ p1) ∧ p5))))) ∨ True) ∨ (p1 ∧ p3)) ∨ (True → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177755069152104568499983738355 : ((((p5 ∧ p2) ∨ (p2 ∧ ((p5 ∧ (False ∨ p4)) → (p3 ∧ False)))) ∧ False) ∨ (True ∨ (p2 ∨ ((p4 ∧ True) ∧ (p1 ∧ ((p4 ∧ p3) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147136932744368593146114718360 : (((True ∧ (((p5 ∨ False) ∨ (p1 ∨ p1)) ∨ (p1 ∨ (p1 ∨ (False ∨ ((False ∨ (p3 ∨ p3)) → p4)))))) ∧ False) ∨ ((p1 → (p5 ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178293939072604739613974328526 : (((p4 ∨ ((p3 ∧ p5) → (((p4 ∨ p1) ∨ True) → False))) ∧ (p3 ∨ True)) ∨ ((False → (False → ((p1 ∧ (True ∧ True)) ∨ p1))) ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588361078219155982100787577325 : ((((((p2 → ((p1 ∨ p2) → p3)) → ((True → (((True → ((True ∧ p5) ∧ p2)) ∨ p2) ∨ p4)) → ((p4 → p2) ∧ p4))) ∨ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323232440225000356699904239929 : (p5 ∨ (((((p4 → p3) ∧ p1) ∧ False) ∨ (p3 ∨ (p3 ∧ (True ∧ (p5 ∨ (((p2 ∧ (p3 ∨ p4)) ∧ True) ∧ (p3 → p5))))))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113703008557623307246774444367 : ((((p2 → (p1 ∨ ((False ∨ (False → (((False → False) ∨ (((p1 ∨ p3) → p2) ∨ p3)) ∧ True))) → p3))) → False) → (p4 → p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165448527608526213291982701131 : ((((p1 ∧ ((False ∨ ((p2 ∧ p5) ∧ p1)) ∨ True)) ∨ False) ∧ ((True ∨ True) ∨ (p2 ∧ True))) ∨ (((p4 → p4) ∧ True) → ((p4 ∧ False) → p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244510486866475849374859762066 : ((False ∧ p3) ∨ ((False ∧ ((((True ∧ p5) → ((p1 ∨ (p4 ∧ p5)) → (p5 ∧ p2))) ∧ (p2 → p4)) ∧ False)) ∨ (((p1 ∧ p4) ∧ p3) → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137771724533287099150867200633 : ((p2 ∨ (((False ∨ ((p1 ∧ (((p1 → p2) ∨ p3) → p1)) → p1)) → p3) ∧ (((p2 ∨ (True ∨ p3)) → p2) ∧ False))) ∨ (p4 → (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98988140874434549690241234129 : ((True → (((p1 → (((p4 → p2) → False) → (p4 ∨ p1))) ∧ (p4 ∨ (True → p3))) ∧ ((p1 ∧ p1) ∧ (True ∧ ((p4 ∨ p5) ∨ p5))))) → p1) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64920636502599864313789123094 : ((p2 ∨ ((p3 ∧ (((p3 ∧ p1) ∨ p4) ∨ (((True ∨ (p3 → True)) → False) ∨ (p3 ∧ False)))) ∨ (p4 → (((False → p4) → p4) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_345648099080009894096903276057 : (p3 → ((p4 ∧ (((True → (p2 → p2)) ∨ (((p4 → p1) ∨ ((p5 ∨ p2) → p5)) → ((True ∨ (p4 → p4)) ∨ (True ∨ p2)))) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709794231474051908813422202521 : ((((p2 → ((False → False) ∧ (p5 ∧ (p2 → p4)))) → ((((p5 ∧ ((p1 ∨ p2) ∨ p1)) ∨ p5) ∧ (((p5 ∨ False) ∨ p4) → p1)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



