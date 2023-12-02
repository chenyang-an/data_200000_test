variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319268730888156200844660637444 : (p4 ∨ ((((((p5 ∧ p3) ∧ p1) ∨ (p3 → p3)) ∧ ((p5 → (p2 ∨ p4)) ∧ p5)) → p3) ∨ (False → (p4 ∧ (True → (p1 → (False ∧ p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_547009885529213401033139844142 : (((False ∨ (((p3 ∨ (((p4 → p1) → p1) ∨ (((p2 ∧ p3) ∧ p3) ∧ p4))) → (((True → (p3 ∨ (False ∨ p1))) ∧ p5) → p4)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_682737269976483036876791084862 : ((((((p1 ∨ p3) ∧ (p5 → False)) ∨ (((p5 ∧ True) → ((True ∧ True) ∧ p4)) → (False ∧ False))) ∧ ((p3 → ((True ∨ p1) → p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152848477770382007657721092611 : (((p2 → p3) → (True → (False → (((p3 ∨ (((p1 ∧ p2) → False) ∨ True)) → p1) → ((True ∧ p2) ∧ True))))) → (p3 ∨ ((p1 ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668775045054007485683842037838 : ((((((p2 → (((p2 → p5) → ((p5 ∧ p2) → (p2 ∨ ((True → p2) → p2)))) → p4)) ∧ (p5 → False)) ∨ p3) ∨ ((False ∧ p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55283892861568304021594578387 : (((False ∧ (p2 → ((p1 → p1) → False))) ∨ (((p3 ∧ p1) ∨ (p1 ∨ p1)) ∨ ((p5 ∧ (True ∨ ((p1 ∨ True) → False))) → (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52983013748768977609231961766 : (((((False ∨ (((p4 → False) → p5) → p4)) ∧ False) ∧ (p4 ∨ p1)) ∧ ((True → ((p3 → False) ∨ (p5 ∨ (True → (p5 ∨ False))))) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686660190510838919072596640098 : (((((p2 ∨ True) → (((((False ∨ p1) ∨ (False ∧ (p1 ∨ p2))) → True) ∨ p1) ∧ (p4 ∧ False))) → (p2 → (((False ∨ True) → p3) → p4))) ∨ False) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p2 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65214347201620592359046898129 : ((p3 ∨ (((False ∧ ((p1 ∧ True) → ((p1 ∧ p5) → (p1 → (True → p2))))) ∨ (p3 ∨ (((True ∨ True) ∧ p4) → (p5 ∧ p4)))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229130260273365402726235855849 : ((True → (p3 ∧ p4)) ∨ (((((p3 ∨ p1) → (p5 ∨ p4)) ∨ (((True ∨ p2) → p1) ∧ (p5 → (True → p4)))) ∧ (p2 ∧ (p2 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245204344279352290536229830247 : ((p2 ∧ False) ∨ (p1 ∨ (((p2 ∧ ((p5 → (((False ∨ p2) ∧ (False ∧ p5)) ∧ p4)) ∧ (p3 ∧ ((False → False) ∨ True)))) ∨ (p1 ∨ True)) ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147009548501149173970221180157 : (((((p2 ∨ p1) → ((True → False) ∨ ((p1 ∨ ((True → False) ∧ (p2 ∧ p2))) → p5))) ∨ (p4 ∨ p2)) ∧ p1) ∨ ((True ∨ p4) ∨ (False ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174940928568206299955157419684 : (((p4 → True) → ((True ∧ ((p4 ∨ False) ∨ (p1 ∧ p1))) ∧ (p1 ∧ (p2 → p4)))) → (((p1 → False) → ((p4 → p1) ∨ True)) ∨ (p3 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41449255552097055908141732126 : ((((((((p5 ∨ p1) ∨ (p2 ∨ p3)) → (False ∨ p2)) → p1) ∨ True) ∧ (((((p4 → p5) ∨ p2) ∨ (p2 ∧ p3)) ∧ p3) → p3)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41263897904183349329247775024 : ((((True ∧ ((p4 ∨ (p1 ∨ (((p5 ∨ p2) ∨ (((p4 ∧ p1) ∧ True) → p2)) ∨ p3))) ∨ p5)) ∨ ((True ∨ p1) → (p1 ∨ p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137887985062048668330700707479 : ((p4 ∨ (((p5 ∨ ((((((p5 ∧ False) ∨ p4) ∨ ((p5 ∧ p2) ∧ (p5 → p4))) ∨ p3) → False) ∧ p1)) ∨ True) → p3)) ∨ (p4 → (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119535988760074961557683268000 : ((p5 → ((p5 ∧ (p1 ∨ ((((p5 ∧ (False → p5)) → p3) ∨ (True ∧ ((p3 ∨ (False ∨ p1)) ∨ True))) ∨ (p1 → p5)))) → False)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191545912696543833840993154420 : ((p1 ∧ (((p1 ∧ p1) ∧ False) ∧ ((p4 ∧ p2) ∧ p3))) ∨ (((True ∧ (False ∧ ((((p1 ∧ False) ∧ (True ∧ p1)) ∨ p5) ∨ False))) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57499674569037107062595603909 : (((p2 → (p4 ∨ p1)) ∨ ((p2 → ((p3 ∧ p3) ∧ (p3 ∨ (True ∧ ((p5 ∨ (True ∧ False)) ∨ (((p5 ∨ True) ∨ p3) ∨ False)))))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347655160136081278887018323349 : (p3 → (((p2 ∨ p5) ∧ (p4 → p1)) → (((p2 ∨ (p3 → False)) ∨ False) → (p2 ∨ (p5 ∧ (((p5 → ((p1 ∨ p1) → False)) → p5) → p1)))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h2.left
      let h12 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h15 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h15
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781774828990425017620702716019 : (((p2 ∨ (p5 ∨ (False ∨ (True → ((p2 ∨ p3) ∧ (p3 → ((p2 ∨ ((p1 ∨ True) → ((False → p5) ∨ ((True ∨ p2) ∧ False)))) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719221411851509078419834153738 : ((((p3 ∧ ((p1 ∧ True) ∨ p3)) ∨ (p5 → ((p1 ∧ ((p2 ∧ False) ∨ False)) ∨ ((p1 ∨ (((True ∧ p5) ∧ True) ∨ (p5 ∨ p3))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313197971395856967192055245291 : (p3 ∨ (((((p4 ∨ p2) ∨ p3) → p4) ∨ (True ∧ (p3 → (False ∧ (p3 → ((p1 ∨ ((p4 ∨ ((p4 ∨ p3) → p3)) ∨ p4)) ∨ p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157283176839058318512288659925 : ((((p5 ∨ p3) ∧ (((True ∨ ((p1 ∨ (False ∧ False)) ∨ (p2 ∨ p1))) ∧ (True ∨ p1)) → p4)) → p3) ∨ ((p1 ∨ (p3 ∧ p1)) → (p5 → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135735445018635075848453384045 : ((((p4 → ((((p5 → False) ∨ ((False ∨ p4) → p1)) ∨ p3) ∧ p5)) → False) ∨ (False → ((p1 → p4) ∨ (p3 → True)))) ∨ ((p1 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1561531276942380818839823010 : ((p5 ∨ ((True ∧ p4) → (p1 → (((p2 ∨ ((((False ∧ p2) ∨ False) ∧ p5) ∨ p2)) ∧ p3) ∨ ((p1 ∧ p1) → True))))) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309635203740840068568117826846 : (p2 ∨ (((True → ((True ∧ p5) ∨ p3)) ∧ (((p3 ∧ p5) ∧ ((p1 ∧ (p3 ∨ (p2 → p3))) ∨ (False ∨ False))) → p4)) ∨ (p5 ∨ (False → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232837038740085261634840425783 : ((p2 ∧ (p4 ∨ p5)) → ((False ∧ (p3 ∨ (p3 ∧ (p2 ∨ False)))) ∨ (((((False ∨ p3) ∨ p5) → (p4 → (p2 → p2))) → True) ∨ (p5 → p2)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248705005281832260607734485063 : ((p3 ∨ p2) ∨ (((((False ∧ p5) → (p3 → False)) → ((p4 → p4) ∧ p3)) ∧ False) ∨ (((p5 ∨ False) ∧ (True ∧ (p5 ∧ (p2 ∧ False)))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177335578700068183495817547718 : ((p3 ∨ ((((False → p5) → (((p4 ∨ p3) → p2) ∨ False)) ∨ True) ∨ True)) ∧ ((p3 ∨ False) → ((False → False) ∨ (p1 → (p5 ∨ (p3 → p5)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667059053315710992245635265457 : ((((((p4 ∨ True) ∨ p5) ∧ ((((True ∨ p3) ∧ p5) ∨ ((((p2 → p5) ∧ True) ∧ p4) ∨ p5)) ∨ (p1 ∧ p1))) ∧ ((p2 ∧ p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651655943232332133686875713324 : (((((p1 ∧ p3) ∨ ((p2 ∧ p1) ∧ (((((p3 → (False ∧ p4)) → p3) ∨ (p5 → (p3 → True))) → (False ∧ False)) ∧ p3))) ∧ (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804005105785192832345986088662 : (((p3 → ((((p5 → (p1 ∨ p5)) ∧ (((p5 → ((p3 ∧ True) → True)) → p3) → p5)) ∧ (p2 ∧ (p2 ∨ p5))) ∨ ((p2 → True) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173230137399667515180721330150 : ((True → ((p4 ∨ (((((p2 ∧ p1) ∧ (p1 → p2)) → False) ∨ p4) ∧ p5)) ∨ True)) ∨ ((((p4 → p2) ∧ (False ∨ (p1 ∨ p1))) ∧ p3) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125533144268159478917115121981 : (((True → False) ∧ ((p1 → p2) ∧ ((p5 → (((p4 → False) ∧ p5) ∧ (p2 → ((((False ∨ p4) ∧ p1) → True) ∧ p3)))) → p3))) → (p2 ∧ p5)) := by
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
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180958510257503210336733971207 : (((p5 ∨ p5) ∧ ((p2 ∨ (p4 → (p2 ∧ (False ∨ False)))) → (False ∧ p5))) → ((p1 ∨ (p2 ∧ True)) → (((p1 ∨ p5) → False) → (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : (p1 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346381857674725035823555764229 : (p3 → ((p2 ∨ (p2 ∧ ((p2 ∧ (((p3 ∧ p4) ∨ (p4 ∨ p3)) → False)) ∧ ((p3 ∨ (((p1 ∧ p2) ∧ p4) ∨ p3)) ∨ True)))) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48794798980166479753887569615 : (((False ∧ (((p5 ∧ p5) ∧ (p3 ∨ False)) ∨ (((False ∧ ((p2 → p3) ∨ p4)) → (p3 → p3)) ∨ (False ∨ p5)))) ∧ ((p2 → p4) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149079477186921413192819605945 : ((((p2 ∨ p1) → False) → ((True ∨ ((p1 ∧ False) → p2)) ∧ ((p2 ∧ p3) ∧ ((p2 ∨ p5) → (p5 → p4))))) ∨ ((p3 → True) ∧ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789883800261636336056044336372 : (((p5 ∨ (((p3 ∧ p1) ∧ True) → (((((p1 ∧ p2) ∧ p4) ∨ ((p5 ∧ (p5 ∧ p2)) → False)) ∧ ((p2 → (True → p1)) ∨ p1)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679083456256872760403420963034 : ((((p1 ∨ (p2 ∧ (((p1 → ((p4 ∨ p2) ∨ (p5 ∧ p3))) ∧ (p2 → ((False ∧ True) → False))) ∧ p3))) ∨ (((p5 → p4) ∧ False) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_174842904104959426182889009892 : (((True ∨ p1) ∨ (p1 ∧ (((((p3 ∧ p4) ∧ (False → True)) → True) ∨ p5) → p5))) → (p2 ∨ (False ∨ (False → (((p1 ∧ p2) ∨ False) ∧ False))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55141173189704833157746298563 : (((((False ∨ (p4 ∨ p3)) ∧ p5) ∨ p4) ∨ (p3 ∧ (((((True ∨ False) ∧ p3) ∧ (p3 ∨ (p1 → p4))) ∧ (p1 ∧ (p5 → False))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265573730150959336179748091116 : (True ∧ (p1 ∨ (((p4 → (((p3 ∨ p1) ∨ p1) ∨ ((p5 ∨ (((True ∧ p2) → (False ∨ p4)) → True)) ∨ p1))) ∨ (p3 ∧ (True → p3))) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326158852630961087870701535032 : (p5 ∨ (p2 → (((True → ((p1 ∧ (p4 → True)) ∨ ((((False → p3) → False) ∧ (p1 ∧ (p2 ∧ p3))) ∧ (False ∨ False)))) ∨ (True → False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44961574928548817996439190789 : ((((p4 ∨ p3) ∧ (((p2 ∧ (p3 ∧ p2)) → (False ∧ ((p5 → p4) → True))) ∧ (p4 ∨ (p4 ∨ (((p5 → p5) ∧ p5) → p2))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304070774339019465023584510809 : (p1 ∨ ((p2 ∨ (((True → p2) ∧ p4) ∧ (((p3 ∨ (p5 → (False → False))) ∨ ((p4 ∧ False) ∨ p3)) ∧ ((p2 ∧ False) ∧ (p3 ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118701974304122117250953278822 : ((p5 ∨ ((((True ∧ (((p4 → ((p5 ∨ False) → p2)) ∧ p4) ∧ (False ∨ p1))) → ((p3 → p1) → (p5 ∧ p4))) ∨ p4) → p5)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651997455971941845487455764023 : ((((True ∧ (True ∧ ((p2 ∧ ((((((p5 ∧ p3) ∧ (False ∧ p2)) → p4) → False) ∨ True) ∨ ((p2 → False) ∨ True))) → p3))) ∧ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115112439472405881602780824047 : (((((p5 ∨ ((False ∧ p5) → False)) ∨ ((p4 ∨ True) → p2)) → False) → (p5 ∧ (p1 ∨ ((False ∧ ((False → p4) ∧ p2)) ∨ p4)))) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((False ∧ p5) → False)) ∨ ((p4 ∨ True) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 ∨ ((False ∧ p5) → False)) ∨ ((p4 ∨ True) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205236417866223685722340559839 : ((((False ∧ True) ∨ p1) ∨ (p4 → p1)) ∨ ((p1 ∨ (p1 ∨ p5)) ∨ (p4 → (((p1 ∧ p2) ∧ (p2 → p2)) → (p1 → ((p1 → p4) → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309543167599271372930018402454 : (p2 ∨ (((p1 ∨ ((((p3 ∨ p4) ∧ p4) → (True ∧ p1)) → (((p4 → ((p4 → False) ∧ p1)) → True) ∧ p3))) ∨ True) ∧ ((p1 → p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190265936199302332676769440331 : (((((True ∧ ((p5 ∧ True) ∨ p2)) → p5) ∨ p1) ∨ p4) ∨ (((False → p4) → (p5 → p2)) ∨ (False ∨ (p2 → ((p1 ∨ (True ∧ p4)) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693670818917981414759978487640 : (((((((p5 → False) ∨ ((p1 ∧ False) ∨ p1)) ∨ (p4 ∧ (p4 ∧ True))) ∨ p4) ∨ ((False ∨ ((False ∧ (p3 → False)) ∧ True)) → (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678781861494588575832143997528 : ((((True ∧ ((False ∧ ((((p2 ∨ True) → (p1 → (((p2 ∧ False) → True) ∨ p1))) ∨ p2) ∨ p3)) ∧ p2)) ∨ (((p3 → p2) → p1) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_46611203031888505106449377892 : (((p2 ∧ (p4 ∨ (p4 ∧ ((p1 ∧ ((((p3 ∧ (p1 ∧ ((True ∧ p2) ∧ p3))) ∨ p1) ∧ (True ∧ p2)) → p5)) ∨ p1)))) ∧ (False ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231726557661216274926344241555 : (((p2 ∧ p3) → p2) → (((p4 ∨ False) ∨ (((p1 → (p2 ∧ ((p2 ∨ (((p3 ∨ True) → False) ∧ (p5 ∧ p2))) ∧ p2))) ∧ p3) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_671333718642803462872640935725 : ((((True → (((p1 ∧ p3) ∨ (False ∨ True)) ∧ (p1 ∨ (((p2 ∨ p5) ∨ p5) → ((p4 ∨ p5) → (p4 → p5)))))) ∨ (True → (True ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263838093716365937341711658889 : (True ∧ (((p5 ∧ p1) ∨ ((p5 ∨ (p3 ∨ p3)) ∧ ((p2 ∧ ((p3 → False) ∧ False)) → False))) → ((True ∧ p4) → (False ∨ ((p3 ∨ False) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
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
      exact h4
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206314029026566219157282259876 : ((p1 ∨ ((p5 ∧ p5) → (False ∧ p2))) ∨ (((p5 ∧ (p4 → p5)) → p3) → ((p2 ∧ ((p2 ∧ (True → (p5 ∨ (True → p3)))) ∧ p4)) → p2))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356433220094089936568352442867 : (p5 → ((((((p4 ∧ p1) → (p2 ∨ p4)) ∧ (False → p3)) → p4) ∨ p4) ∨ (True ∧ ((p5 ∨ (((p3 → (True ∧ p4)) → p4) ∨ p1)) ∧ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118384630913202194328273319459 : ((p2 ∨ ((((p1 ∧ (p4 ∨ (p3 → True))) → p2) ∧ True) ∧ (((p5 → p4) ∧ p1) ∨ (((p3 ∧ p3) ∧ p4) → (p2 → p1))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46839734515174965797122268943 : ((((((((True → p2) → (p3 ∨ p2)) ∧ p4) ∧ p5) → ((False ∧ ((True → True) ∧ (p4 ∨ False))) ∧ (False ∨ p3))) ∧ p5) ∨ (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200511854885558231029958317312 : (((False ∨ True) → ((p1 ∨ (p1 ∨ True)) → False)) → (p1 ∧ ((((p2 ∨ p1) ∨ False) ∨ ((p3 ∧ (((p4 ∨ p2) ∧ p4) ∨ p5)) → p2)) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (p1 ∨ (p1 ∨ True)) := by
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
theorem thm_5_vars_42416507066896589484364879316 : (((p5 ∧ (((True ∨ ((p3 → p1) ∨ p3)) → (((((p3 ∧ p3) → False) ∧ p3) → ((False → (False ∨ True)) → True)) ∧ p4)) → p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111259269591257742213437203907 : ((((p3 ∨ p2) ∨ ((p4 ∨ ((True → ((((p3 → p4) ∧ (p2 ∧ (p5 → p5))) ∨ p4) → p2)) ∨ (p4 ∨ p1))) ∧ True)) ∧ p4) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346622981518783013318775128212 : (p3 → (((p1 ∨ (p1 → p4)) ∨ (((((((True ∨ (p2 → False)) ∧ p1) → p5) ∨ p5) → True) ∧ (p4 ∨ False)) → False)) ∨ ((p2 ∧ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118520379346056956452682475368 : ((p3 ∨ ((p1 → p2) ∧ (((True ∧ (p1 ∧ (p5 → (p1 ∨ (True ∧ p5))))) → p3) ∨ ((p3 → (p2 → p3)) → (p2 → p1))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737897092551627371770578919867 : ((((True ∧ p2) ∨ ((p5 ∨ p4) → ((((p1 ∧ (((p5 ∧ (p4 ∧ p2)) → p3) → p4)) ∨ ((p3 ∨ True) ∨ p3)) → (p1 → p5)) ∨ True))) ∨ p4) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773655186012437648000935766829 : (((False ∨ ((True → ((((p3 ∧ (((p3 → p1) ∨ p3) ∧ True)) ∧ ((p5 ∧ (True → ((False ∧ True) ∨ p3))) → p5)) ∨ p5) ∨ p5)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149139084948878771735946366608 : (((p5 ∧ p1) ∧ (((((False → False) ∧ (p5 → True)) → (((p3 ∧ (p1 → p1)) ∨ p3) ∨ p2)) ∧ p5) ∧ True)) ∨ (True ∨ (p4 ∧ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54404144904076554200188964228 : (((((False ∨ p1) ∧ (p5 ∨ (True ∧ p2))) ∧ p3) ∨ (((p3 ∧ p2) → ((p1 → (False → p5)) ∨ False)) → (False ∨ (p1 ∧ (False ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342277541569471025543161411149 : (p2 → ((((((p1 → ((p1 ∧ p5) ∨ (p4 ∧ p2))) ∨ p5) → p3) ∧ ((p1 → p1) ∨ False)) → p1) ∨ ((p2 → p2) ∨ ((p3 ∨ p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174800259709557847377680344475 : (((True → False) ∧ ((((p3 ∨ False) → ((True ∨ p1) ∨ (p3 ∨ False))) → True) → p1)) → (((p2 ∧ (p3 → p4)) ∨ (False ∨ (True → p3))) ∧ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308827404502247061060405421746 : (p2 ∨ (((True → ((p2 ∧ (p4 ∨ (((p3 ∧ (False ∨ p2)) ∨ (p1 ∧ (p1 ∨ False))) → ((p2 ∧ (p3 → False)) → p4)))) ∧ p1)) ∨ False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677516231200349992445686179768 : ((((((p1 → p5) → (p2 → (((p2 ∧ p2) → (True ∨ ((p5 ∧ (p4 → p2)) ∨ p5))) ∧ False))) ∨ False) ∨ (((p2 → p4) ∧ p3) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_571340035152825523628288837697 : (((p1 → (((p1 ∧ ((((p3 ∨ (p5 → False)) → False) ∨ p5) ∨ ((p2 ∧ p4) ∨ (True ∨ p5)))) ∨ (p1 ∨ (p5 ∨ p3))) ∨ (p3 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499220614844823677911213494925 : (((((p2 ∨ p1) ∧ p1) ∨ (((((p5 ∨ (False → (False ∨ ((p4 → False) ∧ True)))) ∨ (p1 ∧ p2)) ∨ (p3 ∨ p2)) ∧ (True → p3)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_185313924876200157947234585622 : ((p3 ∧ (((True ∧ p5) → (p2 → ((p2 ∨ p5) ∨ True))) → p2)) ∨ (True ∨ (((p1 ∧ p2) ∨ p2) ∨ ((p2 ∧ p3) → ((p3 ∧ p4) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180932123857545764730271424450 : (((p4 ∧ True) ∧ (p3 ∨ ((p4 ∨ False) ∨ ((p3 ∧ (p4 ∧ p5)) → True)))) → ((((p2 ∧ (p1 ∧ True)) → (p3 ∧ (True ∧ p4))) ∨ True) ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
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
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309802429798950221817877346727 : (p2 ∨ ((((True ∧ (True ∨ p4)) ∨ p4) ∧ ((p5 ∨ p2) → ((p5 ∨ False) → ((p4 ∧ True) ∨ (p1 ∧ False))))) ∨ (True ∨ ((p2 ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66308660907633208363278029582 : ((p5 ∨ ((p3 ∨ p5) → (((p3 → p3) ∨ False) → ((((p5 ∧ ((p4 ∨ p1) ∨ p5)) ∨ (p3 ∨ (False → p1))) ∧ (True → True)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62393498865639470684322050443 : ((p3 ∧ ((((p4 ∨ True) → (p5 ∧ (False ∨ (True ∨ p2)))) ∨ p5) ∧ (((True ∨ (p5 → (p4 → p2))) → (p1 → True)) ∧ (False ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322389999922235030757286227053 : (p5 ∨ (((p5 ∨ (p1 → ((p4 ∨ (p1 → False)) ∨ (True ∧ (((False ∨ True) ∨ p2) ∨ False))))) → (p3 → ((False ∨ (p3 → False)) → p1))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809218119052319154368971008851 : (((p5 → ((((((p3 → p1) ∧ ((p1 → p3) → (p5 ∨ p5))) ∨ ((p1 ∧ p3) ∨ (p1 ∧ False))) → p1) ∨ ((p1 → True) ∧ False)) ∨ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_61067948558145744033776038690 : ((False ∧ ((p4 ∨ ((p5 ∧ (((((p3 → p4) ∧ True) ∨ (((p2 ∨ p1) ∨ True) ∧ True)) ∧ p3) ∧ p4)) ∧ p3)) ∨ (p5 → (p3 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149911033480669605430662019842 : ((p3 ∨ (((p1 ∨ ((((((p4 ∧ p4) ∧ p5) ∨ p3) ∧ False) → (p3 → p5)) ∧ (p5 ∧ p3))) → p4) ∨ p4)) ∨ (p4 → (True → (p4 ∨ p1)))) := by
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
theorem thm_5_vars_149254288577328267027982464039 : (((p3 ∨ False) ∨ (((((True ∧ p1) ∨ (p2 → p5)) ∧ p2) ∨ (p1 ∧ ((p3 ∧ (p5 ∨ p5)) → True))) → p2)) ∨ (p1 → (p5 → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59074856020651959343104106809 : (((p5 ∧ p1) ∨ (((((p5 ∨ p4) ∨ (((p5 ∨ p5) ∧ (p4 ∧ p4)) ∨ p1)) ∨ ((p1 ∨ (False ∨ (p3 → True))) ∧ p4)) → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2191561070437285917140824879 : (((False → (p3 ∧ (p4 ∧ p3))) ∧ ((p5 ∨ ((p3 → (p2 ∧ p2)) → False)) ∨ p5)) ∨ (p2 → (((p3 → True) ∧ True) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_356892306703481968034000736064 : (p5 → (((p5 ∨ (p5 ∨ p5)) ∨ True) → ((p2 ∨ (p1 → False)) → ((True → ((p5 → p5) → ((p2 ∧ (p1 ∧ p4)) ∨ p5))) ∨ (True ∧ True))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48965084438713040158824627323 : (((((((p4 → ((p3 ∨ (p1 ∨ p5)) → (p3 ∧ ((p2 ∧ p3) ∨ p1)))) ∧ True) → (p1 → p4)) ∨ True) ∨ p2) ∨ ((p5 ∧ p1) ∧ p3)) ∨ False) := by
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
theorem thm_5_vars_112688345005784320673078268437 : (((((p1 → ((p4 ∨ p4) → p4)) → ((p3 ∧ False) ∧ (False ∧ ((False → p2) ∧ True)))) ∧ ((p5 ∧ (p3 ∨ p5)) → p5)) → p1) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → ((p4 ∨ p4) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247723247267857187806679223192 : ((p1 ∨ False) ∨ (((p5 → (p5 ∨ p1)) → ((False ∧ (False → True)) ∧ (p5 ∧ (p2 ∧ ((((p5 ∨ False) → p4) ∨ True) → p4))))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204329215317417995284544940327 : (((p4 ∧ ((p4 ∧ p3) ∧ p4)) ∧ p1) ∨ ((p3 ∧ (p1 ∧ ((False ∨ p4) → (p1 → (((p3 ∧ False) ∧ p2) ∨ (p1 ∧ (True → p1))))))) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349268741817491985468846347401 : (p3 → (p2 → (((((p2 ∨ (p2 ∧ ((False → p2) ∧ (False → (False ∧ True))))) ∧ (p1 ∨ p1)) → (p4 ∨ False)) ∨ (p3 ∨ (p5 → p5))) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217503149479128189821589201052 : ((((p2 ∨ p1) ∧ p1) → p5) → (((p1 ∨ p5) ∨ (p5 ∨ p3)) ∨ ((p1 ∧ p5) → (p5 ∨ ((p2 ∧ ((p1 → True) ∧ False)) → (p4 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41388206719387477762360479407 : ((((((p5 ∨ p1) ∨ ((p5 ∨ p2) → ((p3 ∨ p1) → p4))) → (p2 ∧ p2)) ∧ (True → ((p4 → (False ∧ p3)) ∨ (p1 ∨ p5)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114055553280338450930201519424 : ((((((((p5 ∨ False) ∨ p2) → ((False ∨ p1) ∧ p5)) ∨ p4) ∨ False) ∧ (p5 ∧ (p3 → (True ∨ p3)))) ∨ (True ∨ (p1 → p1))) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343035358339182425161522652931 : (p2 → (((p3 ∨ p5) ∨ (False ∧ p5)) → ((p5 → (((False ∧ ((p1 → p3) ∨ p2)) ∧ True) → True)) → ((p4 → p3) ∨ (p3 ∨ (p5 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



