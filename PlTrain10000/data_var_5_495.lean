variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750020357002154886685498763813 : (((True ∧ ((((p5 ∧ ((True → p5) ∨ (p5 ∨ False))) ∨ p2) → (False ∧ (p4 ∨ ((False ∨ ((p2 ∧ False) ∨ (p2 ∨ False))) → p3)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679713142957318114622786865049 : ((((((True → (p1 → (p2 ∨ ((p5 ∧ p4) ∨ (p3 → (True ∨ (p2 → (False ∧ p3)))))))) → p4) ∨ False) → (p5 ∧ (p4 ∧ (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349136489919960003971109245193 : (p3 → (True → (p2 ∨ (((p5 ∧ (((p1 → (p2 ∨ (p4 → p3))) ∨ (((p3 ∨ p1) ∨ p5) ∧ True)) ∨ True)) ∧ ((p2 ∨ p5) → p4)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : (p2 ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h17 : (p2 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h18 := h5 h17
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h20 : (p2 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h21 := h5 h20
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h23 : (p2 ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h24 := h5 h23
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h26 : (p2 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h27 := h5 h26
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63351213429713335299430064920 : ((p5 ∧ (p1 ∧ ((((True ∧ p3) ∧ p1) ∨ ((p4 ∨ (False → ((False ∨ (p3 ∧ p3)) ∨ p2))) ∨ p3)) ∧ (p4 ∨ (False → (p2 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54907478396940756899589953186 : ((((p5 → (False ∧ (p5 ∧ p1))) ∨ p3) ∧ ((((False ∨ (False ∧ False)) → p2) ∨ p1) → (((True ∨ p5) ∧ (p4 ∧ p5)) ∨ (p3 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353932289405614772681771737270 : (p4 → (p2 → ((p3 ∧ p3) → ((p4 → (p2 ∧ (p4 → True))) ∧ ((p5 ∨ (p4 → (False ∧ (p1 ∨ ((p3 → p1) ∧ (p2 → False)))))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249475751078972323802239058884 : ((p5 ∨ p1) ∨ ((True → (p5 ∨ ((p2 ∧ p2) ∧ (p3 ∧ (((((True ∧ (p2 → p4)) ∧ False) ∧ (p4 ∧ p1)) ∨ (p5 → p3)) ∧ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64744640563104482869935191488 : ((p2 ∨ (((((((False ∧ p2) ∧ p2) ∧ p4) → ((p5 ∧ p1) → p2)) ∧ (p5 ∧ (((p1 ∧ p5) → p5) → True))) → (p5 ∧ p2)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118364241294783832732980802786 : ((p2 ∨ ((((True → (p2 → False)) → (((p1 ∨ (p3 ∧ True)) ∨ (p2 ∨ (True → p1))) ∨ (p3 ∨ p4))) → p4) → (p4 ∧ p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172276980901816009146256487697 : ((((p4 ∧ p1) ∨ (((p3 ∨ p5) ∧ p2) → False)) ∨ ((p4 ∧ (p1 → p1)) ∨ p1)) ∨ (((p2 → ((p5 → (p5 ∧ p2)) ∨ p4)) ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214343153390373440974926760791 : (((p2 ∨ (False → p1)) → p2) ∨ (p1 → (p1 ∧ ((p3 ∨ ((p2 ∨ (p2 ∧ p3)) ∨ (True ∨ (p4 ∧ p1)))) ∨ (p4 ∧ ((p4 → False) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_157000779534578877750512306996 : (((((True → (True ∨ p5)) ∨ True) → (p2 ∧ ((False ∨ (p2 ∨ ((True ∧ p2) → p5))) ∧ False))) ∨ p1) ∨ (True → ((p1 ∧ True) → (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299097914824350728362703049882 : (False ∨ ((((((p3 ∧ p1) ∧ (((p3 ∧ (p2 ∨ ((False ∧ p4) ∨ True))) ∨ False) ∧ p1)) ∧ p5) → (((False → p3) → p2) ∨ p4)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3921071737964364602661032788 : (False ∨ (((p4 → p5) ∨ ((p1 ∨ p2) ∧ (((p4 ∨ p5) → (False ∧ ((p4 ∧ p4) → p3))) ∨ True))) → (p1 ∨ (p3 ∨ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217723912282527215155767004933 : (((p1 ∧ (p2 ∨ True)) → p1) → (p5 → (((p4 ∧ (True → True)) → (False ∧ p4)) ∨ ((p3 ∨ (False → (False ∧ ((p1 → False) ∧ p3)))) ∨ p5)))) := by
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
theorem thm_5_vars_788439798442653382660211138772 : (((p5 ∨ (((((p2 ∧ p3) → False) → p4) ∧ ((p3 → False) ∧ (((p4 ∨ (p1 ∨ p2)) ∨ True) ∨ (True ∨ (p5 ∧ (p4 ∧ False)))))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_51081803034566530915966830826 : (((p5 → ((p2 ∧ ((((p3 → ((p1 ∨ True) → True)) ∧ (True ∨ p2)) ∨ p4) ∨ p5)) → p1)) ∧ ((p5 ∨ p2) ∨ (p1 ∧ (p5 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48623210298038138091899740933 : (((((p4 ∨ ((p3 → (((p5 ∨ p2) ∧ p5) ∧ (p5 ∧ True))) → (p2 ∧ p1))) → p4) ∧ (p3 → (p1 → True))) ∧ (False → (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_12340677435751955924186696836 : (((((True ∨ (p3 ∨ p2)) → False) ∧ (False ∨ (p5 → ((((p5 → p4) → (p3 → (p1 ∨ True))) → p2) → (p1 ∧ (p2 → True)))))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (p3 ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66809297597921261780579316939 : ((True → (p4 ∨ ((((False → p3) → p2) ∨ p4) → (p5 ∧ (p1 ∨ (((False → False) → ((p4 ∧ p4) → ((p4 ∨ p3) → True))) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476837270321692301439293812846 : ((((False ∨ (p2 ∧ (((p2 ∨ p4) ∧ True) ∨ (p2 ∧ False)))) ∨ ((True ∧ (False ∨ (True ∧ (((p4 ∧ (p1 ∨ False)) ∧ p3) → False)))) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191274562989751313764422839211 : (((p1 ∨ p4) ∧ (p5 ∨ ((False ∨ (p3 → p4)) ∧ True))) ∨ (True ∨ (((True ∧ (p3 ∨ (p4 ∨ (((p4 ∧ False) → False) ∨ p1)))) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172227349080263257203676860197 : (((p5 → ((((True ∧ p1) → p1) ∨ True) ∨ (p3 ∧ p5))) → ((True ∧ p3) ∧ p1)) ∨ (p2 ∨ (False → (p2 ∨ (((p5 ∨ True) ∧ True) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119429442648089217578859498428 : ((p4 → (((((p5 ∨ (False ∨ False)) → False) → (False ∧ ((p1 ∨ True) ∧ ((True ∨ True) ∧ p2)))) ∧ p2) ∧ (p5 → (True ∨ p3)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58397296619316872936857069771 : (((p2 ∨ True) ∧ ((p3 ∧ (p2 ∧ p2)) ∨ (False ∧ (((p3 ∧ (p4 ∧ (((p1 ∧ True) ∨ p5) → p1))) ∧ (p4 ∧ (p4 → p1))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47092346121136299066062457825 : ((((p5 ∧ ((p4 → (p4 → (p4 ∧ (True → True)))) ∨ (p3 ∨ ((True ∨ (p4 → p4)) → (False ∨ p5))))) → (p4 ∧ p1)) ∨ (p4 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592859253645789437015351384959 : ((((((((p3 ∨ False) → p4) → p5) ∧ ((((p3 → p5) → ((p5 → p2) → p1)) → p1) ∨ (p5 ∨ p1))) ∧ (False ∧ (True → False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165376017835200951702881770946 : ((((False ∧ (True → (p5 ∨ (p3 → (True → p1))))) ∧ (p5 ∧ p3)) ∨ ((p5 ∨ True) ∧ p5)) ∨ (((p3 ∨ p3) → p1) → ((p3 ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241587179470459154938829206543 : ((False → p4) ∧ (((((p1 ∧ p1) → (((((p3 ∧ (p5 → p5)) ∧ True) → p5) → False) ∨ p2)) ∨ (p5 ∨ (p4 ∧ True))) ∨ True) ∧ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60666041116228668846419189286 : ((True ∧ ((p5 ∧ (((((False ∧ p1) → (p2 ∧ p2)) → (False ∧ True)) ∨ True) ∨ (p4 ∨ True))) ∧ ((p2 → p2) ∧ ((p3 ∨ False) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180624601226527379279738074298 : (((p4 ∨ ((True ∨ True) → (False ∧ p1))) ∧ ((p4 ∧ p1) ∨ (p1 → p2))) → (((p1 → ((p4 → (p4 ∨ True)) ∧ p2)) ∨ False) ∨ (p1 ∧ p1))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h18 := h13 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h21 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h22 := h13 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810693206312776469614250175913 : (((p5 → ((p1 ∧ (p5 ∧ p4)) ∨ ((True ∧ ((p4 ∧ ((p3 ∧ (p2 ∨ p1)) → p1)) ∨ (p5 ∧ p1))) ∧ (p5 ∧ (p5 ∧ (False ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792585481173283852821789609279 : (((True → (((((True ∨ p1) ∧ True) → (p2 → p4)) → p2) → (((p3 → (p3 ∧ (p2 → False))) → p2) → (p3 → (p2 ∧ (p2 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299165326453760198128367287561 : (False ∨ ((((((p5 → (((p1 ∧ p5) → False) → (p3 ∨ False))) → p5) → (p5 ∧ ((((p1 → p5) ∧ p4) → p4) ∨ False))) ∨ p4) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345711214885106184970707460844 : (p3 → ((p1 → (((p4 ∧ (p3 ∨ p2)) → (p4 ∧ (p1 → ((p5 ∨ p5) ∨ p3)))) ∧ (((False ∨ p4) ∧ False) ∨ (True ∨ (p4 → p1))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144522752058827267619277403185 : ((((((((True → ((p5 ∨ p3) ∨ p3)) ∨ ((p5 → False) ∧ p4)) → True) ∨ p4) ∨ p4) → p5) ∨ (True ∨ p3)) ∧ ((True → True) ∨ (p3 → p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315832875691603995496497751649 : (p3 ∨ ((p5 ∨ p5) → ((((p1 ∨ p5) ∧ (p5 ∧ (((((((False → p4) → p4) ∨ p4) ∧ p3) ∧ (p3 ∧ p1)) → p1) ∨ True))) → False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 ∨ p5) ∧ (p5 ∧ (((((((False → p4) → p4) ∨ p4) ∧ p3) ∧ (p3 ∧ p1)) → p1) ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 ∨ p5) ∧ (p5 ∧ (((((((False → p4) → p4) ∨ p4) ∧ p3) ∧ (p3 ∧ p1)) → p1) ∨ True))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190810819314308207741912070184 : ((((False → p4) → (False ∨ (False ∧ p5))) ∨ (p5 ∨ True)) ∨ ((p3 ∧ p4) → (p4 ∧ ((True ∧ (False → p5)) → (p2 ∧ (p5 ∧ (p1 → p4))))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330250719204235056856569601387 : (True → (False ∨ ((((p1 ∨ ((False → (p2 ∨ (p4 ∨ p2))) ∧ (p4 → p2))) → p3) ∨ (((p5 → True) ∧ False) → True)) ∨ ((p3 → p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40308138456003981385026038487 : (((((((p5 → (False → ((((p3 ∧ (p5 ∧ p4)) → p5) → p1) → True))) → p1) ∨ ((p2 ∨ (True ∨ True)) → p3)) ∧ p3) ∨ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309614784079403082275824797524 : (p2 ∨ (((True ∧ (p4 ∧ ((True → (True → p5)) ∨ ((p2 ∨ ((True → p5) ∨ p4)) ∨ (False ∨ (p5 ∨ p4)))))) → p2) ∨ (False → (False ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234304895492663887519659462940 : ((p1 → (True ∧ p5)) → (False ∨ (((p5 ∧ ((False ∨ (p1 ∨ (p5 ∨ False))) ∨ (p1 ∨ (((p2 ∧ False) ∧ p2) → (p1 ∧ p1))))) → p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748432281665724494983158590149 : ((((p2 → p4) → ((((((p2 ∧ (p1 ∨ p2)) ∨ (p1 ∧ (((False ∨ p2) ∨ p3) → True))) ∧ False) ∨ True) ∨ p4) ∧ (True ∨ (p1 ∧ p5)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_825005694940280482215373837036 : ((((((p1 ∨ True) ∨ False) → (((p4 → (p1 → ((p5 ∨ (True → ((p5 ∧ (False ∨ True)) ∨ p1))) ∨ p4))) → (p5 ∨ True)) ∧ False)) ∧ True) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46640765481564983048346213222 : (((p5 ∧ (((p3 ∧ p4) ∧ (p3 ∧ p3)) ∨ (p4 ∧ ((p4 ∧ True) ∨ (((p3 ∨ p3) → (p4 → p4)) → (p4 ∧ p2)))))) ∧ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662823783530559371268555665343 : ((((((p5 → p5) ∨ p5) ∧ (p4 ∧ ((p2 → ((p5 ∨ (p2 ∨ (True ∨ p4))) → (False ∨ (p4 → p2)))) ∨ (p4 ∧ p1)))) → (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136044526623796562719000667342 : (((False → ((p5 → ((True → False) ∨ (p5 ∨ p2))) ∨ p3)) → ((p1 → p4) ∧ (((p2 ∧ (p5 ∧ p1)) ∨ p2) ∧ False))) ∨ ((p1 ∧ False) → False)) := by
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
theorem thm_5_vars_715390184141664009904163827022 : ((((((p4 ∧ p4) ∧ p4) ∧ False) ∧ ((((p5 ∨ p5) ∧ (False → p3)) → p2) ∧ ((p5 ∨ ((p1 → (p5 → p3)) ∧ (p5 ∨ p2))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62127912365555092359529219098 : ((p2 ∧ (p3 ∨ ((p1 → p5) ∧ (p2 ∨ (((((True ∨ True) → ((p4 ∧ (p2 ∧ (p1 ∨ p3))) ∧ (p3 ∧ p4))) ∨ True) ∧ True) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205458587935666398888144071421 : (((False → (True → p1)) → (p5 ∧ False)) ∨ (p1 → (((p2 ∨ (p1 ∨ ((p2 ∨ (p4 ∧ (p4 → False))) ∨ True))) ∨ (False → p5)) ∧ (p1 ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80927305070337981658611175962 : (((((True ∧ (p2 ∨ p4)) ∧ ((p3 → p1) → ((p1 → (False → (p4 ∧ (p1 ∧ False)))) ∧ (p2 ∨ p5)))) → False) ∧ (p2 ∧ (p3 → p3))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∧ (p2 ∨ p4)) ∧ ((p3 → p1) → ((p1 → (False → (p4 ∧ (p1 ∧ False)))) ∧ (p2 ∨ p5)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- False on the left can always be used.
    apply False.elim h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h6
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785414888077536690845219163816 : (((p4 ∨ (((True → ((p5 → p3) ∨ ((((p5 ∨ True) ∧ (p4 ∧ p5)) → True) → ((p5 → False) → p3)))) ∨ ((True ∧ p3) → True)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_868326643678508514566067590463 : (((((p5 ∨ p2) → ((p1 ∧ True) ∨ (((p1 ∧ False) → ((p4 ∨ (p5 → p4)) → (True ∨ False))) ∧ (p3 ∨ (p3 → (p2 ∨ p3)))))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p2) → ((p1 ∧ True) ∨ (((p1 ∧ False) → ((p4 ∨ (p5 → p4)) → (True ∨ False))) ∧ (p3 ∨ (p3 → (p2 ∨ p3)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h5.left
        let h9 := h5.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h5.left
        let h12 := h5.right
        -- False on the left can always be used.
        apply False.elim h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h15.left
        let h19 := h15.right
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h15.left
        let h22 := h15.right
        -- False on the left can always be used.
        apply False.elim h22
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255563031756270447469678790047 : ((p5 ∧ p3) → ((((((p3 → p1) → (p4 ∨ p3)) → (((p1 → p1) → p2) ∧ p5)) ∧ False) ∨ (p3 ∧ False)) ∨ (((True ∧ False) ∨ p3) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345386840973833025073412794858 : (p3 → (((True → (((p2 ∨ p1) ∨ (p5 ∨ (True ∧ ((False ∨ (True ∧ (p3 ∧ True))) → (p1 ∧ False))))) ∨ ((p3 → p3) ∨ False))) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908309144134548338166959707873 : ((((((False → (((((p3 → p4) ∧ (p3 ∧ False)) → p4) → True) ∨ False)) ∧ (False → p1)) ∧ p1) ∧ (True ∧ ((False ∨ p2) → (p2 ∧ False)))) → p1) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344696357433571484775051470475 : (p2 → (p2 → (p3 ∨ (((((False ∧ (False ∧ p2)) → (False → (((p3 ∧ p4) → ((p5 ∧ p3) ∨ p2)) ∨ False))) ∨ p4) → (p2 ∧ p1)) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199800086122787634963299417602 : (((((p2 ∨ True) ∨ False) ∨ False) ∧ (p4 ∧ p5)) → ((((p1 ∧ False) ∨ p2) ∧ (p2 → (True ∧ p1))) ∨ (((p3 ∨ p4) ∧ (p2 ∨ True)) ∨ p4))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h3.left
        let h8 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h3.left
        let h11 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770039814117809549567820153636 : (((p5 ∧ (p3 → ((((((p5 ∧ False) ∧ p2) ∧ p2) ∨ ((True ∨ (p3 ∨ (((p5 → p2) ∨ False) → (p2 → p3)))) ∨ True)) ∨ True) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49193060927666741886119669476 : ((((p2 ∧ (True ∧ False)) ∧ ((p5 ∨ p4) → ((p4 → (True ∨ True)) → ((True ∨ ((p5 → p5) ∧ p4)) ∧ p4)))) ∨ ((p4 → p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748778736753883573588206273841 : ((((p4 → True) → ((False ∧ (p4 ∧ (((p2 ∨ False) ∨ (p2 ∧ p5)) → (False ∧ ((p5 → p1) ∧ (((p3 ∧ p3) ∧ p2) ∧ p3)))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63160867598584908262389726720 : ((p5 ∧ ((((p4 ∨ ((((p2 → (p2 ∨ ((p2 ∧ p1) ∨ (p5 ∧ p2)))) → p3) ∧ True) ∧ (p3 ∧ p4))) ∧ p1) ∨ p1) ∨ (p3 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257145866944758033682984415889 : ((p2 ∨ p1) → ((p2 ∧ (((p4 → ((p2 ∧ p2) ∨ p1)) ∧ (p2 ∧ False)) → (p2 ∨ p2))) → (((p4 ∨ p2) → p3) ∨ (False ∨ (p5 → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186612548690150867961108204405 : (((((True ∨ p4) → p5) ∨ (True → (p4 ∧ p4))) → (p2 ∧ p1)) → (p2 → (p2 ∨ (((True ∨ (p4 ∧ p1)) ∧ ((False → p3) ∧ False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259040260629203092594435368665 : ((True → p4) → ((True ∧ p1) ∨ (((p4 ∨ p5) → ((((p2 ∧ p4) → False) ∧ p4) ∧ p5)) ∨ (True ∨ (p2 ∧ ((p3 ∨ (p3 → p4)) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113946916384888392819134979294 : (((((p4 → True) ∨ False) ∧ ((((p3 ∧ True) ∧ p2) → ((False → (True → p5)) ∨ (p5 → p3))) → p4)) ∧ (p5 → (p1 ∨ p5))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149984694064925728177414625996 : ((p4 ∨ ((False ∨ p2) → (True ∧ (((p1 ∧ (False ∧ p4)) → (False ∧ False)) ∧ (p1 ∨ (p1 ∧ (False ∧ p3))))))) ∨ ((False ∧ (True ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18121507525246162896773429725 : (((p3 → (((((p4 ∨ (p4 ∧ (True ∧ (False ∨ (p5 ∨ (p4 ∨ p4)))))) ∧ p1) ∧ p3) ∧ False) ∨ p1)) ∨ ((p4 ∨ p5) → (False → p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_351806819750999281395821678326 : (p4 → ((((((p5 ∨ ((True ∧ False) → False)) ∨ p2) → p5) ∨ p3) ∧ p3) ∨ (False ∨ (((p1 ∨ ((p2 → True) → (False ∧ True))) ∧ False) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1612730118397704719151769259 : (((((True → ((True ∧ (p2 ∨ (((False ∧ p1) → p2) → (p2 ∨ True)))) ∨ p4)) ∨ (p2 → p3)) ∨ p1) → (False ∨ p4)) → (p3 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → ((True ∧ (p2 ∨ (((False ∧ p1) → p2) → (p2 ∨ True)))) ∨ p4)) ∨ (p2 → p3)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147894016477942225976710220914 : (((((((False ∧ p3) ∧ ((p2 ∧ (False ∧ p4)) ∨ p1)) ∧ (False ∧ p1)) ∨ (p5 ∨ p1)) ∨ p5) ∧ (False ∨ True)) ∨ (((False → p1) ∧ p1) → p1)) := by
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
theorem thm_5_vars_779103625403053799316881046963 : (((p2 ∨ (((p4 ∨ ((((((p2 ∧ (p2 ∧ p3)) → (p4 ∨ p4)) ∨ True) ∧ (((True → p5) → False) ∨ p2)) → False) → p2)) ∧ p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338373286764517300574598936850 : (p1 → ((p2 ∧ (p4 ∧ (p5 ∧ p5))) ∨ (((True → p5) → ((p1 → ((False → p2) ∧ (p5 ∧ p2))) ∨ (p5 → ((p1 ∧ p3) → True)))) ∨ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792790156501877738839071301676 : (((True → (((p5 ∨ p4) → p1) ∧ (((((p4 → p4) ∧ ((p2 ∧ p5) ∧ (False ∧ (p2 ∧ p2)))) ∧ True) ∧ (False → p2)) ∨ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137799250438030854097408285532 : ((p2 ∨ (p2 ∨ (p2 ∨ ((((p3 ∨ False) ∧ (True ∧ p1)) ∧ (p5 → p1)) ∨ (True ∨ ((p4 ∨ False) → (p5 ∨ p1))))))) ∨ ((p4 → p2) ∧ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42081766057921967339978885417 : ((((p2 → p4) ∨ ((((((((False → p3) → p5) ∨ True) ∧ p1) ∨ (p4 ∧ p2)) ∧ False) ∨ ((p3 → True) ∧ p5)) ∧ (p2 ∨ False))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300603077338031956809864544442 : (False ∨ ((((p4 ∨ (p1 ∧ p5)) ∨ p4) ∧ (p3 → ((p5 ∨ p5) → ((((p4 ∨ p2) ∨ p5) ∧ True) ∧ p2)))) → (((p5 ∨ p1) ∨ False) ∨ True))) := by
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
theorem thm_5_vars_215522960439865328338569428241 : ((p4 ∧ (p4 ∧ (p1 ∨ p3))) ∨ (((((p2 ∨ (p4 ∧ (False → (p1 ∨ (((p2 ∧ (False → True)) → False) → p1))))) → False) ∧ p4) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185807687618560814773977328463 : ((p5 → (p2 ∧ ((True → (p1 ∨ True)) → ((p5 ∨ p4) → False)))) ∨ (((((p5 ∨ p2) ∧ p5) ∧ False) ∧ (p1 → ((p1 ∨ p2) → p1))) → p4)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65358166980238494474154130494 : ((p3 ∨ ((((p4 → True) → (p5 ∨ False)) ∧ (p2 ∨ (p5 → (p4 ∨ (p3 → p3))))) → (p2 → ((p3 ∨ (p4 ∨ (p4 ∧ p2))) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169088769345287235281233784976 : ((p4 → (((((p3 ∧ p4) ∨ p1) ∧ (((p5 → p2) → (p1 ∨ p3)) ∨ p4)) ∨ p2) ∨ p5)) → ((False ∨ (p1 ∧ p3)) ∨ ((p5 ∨ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111011279624347291365651957538 : ((((((((p2 → p5) ∨ (p3 → p4)) ∧ p5) → p5) → (False ∧ ((p4 ∧ p1) ∨ (p3 → False)))) ∨ (False ∧ (p4 ∧ False))) ∧ p1) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51104684936411185169909374481 : ((((p5 ∧ (p3 ∨ (((p5 ∨ (True ∨ p2)) → (((False → False) → p1) ∧ p5)) ∨ p5))) ∧ p5) ∨ (((False ∨ (p4 → p3)) ∨ True) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230766561885982959629334006729 : (((True ∧ False) ∨ p4) → ((((p4 ∧ (True ∨ ((False → ((((p2 → p3) → p4) ∧ p1) ∨ p5)) → ((p1 ∧ p5) → p3)))) → p2) ∧ True) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136264662057494640564931782977 : (((((p1 → (p3 ∨ p4)) → False) ∨ p1) → (((p2 → (p3 ∨ (((p5 ∧ True) ∧ (False ∧ p5)) ∧ False))) ∨ p5) → p5)) ∨ (False → (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204242331960725342698882952470 : ((((p1 ∨ p3) ∧ (p1 ∧ p1)) ∧ False) ∨ ((((p3 → (False ∧ False)) → (((p1 ∨ (p2 ∧ p2)) ∧ (p2 ∧ p4)) ∧ (p1 → p1))) ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113515080171048074423777494037 : (((((True → ((True ∨ (p4 ∨ p2)) ∧ (True ∨ (p4 → p3)))) → p2) → ((p3 ∧ ((p1 → p3) → p3)) ∨ p5)) ∨ (True → True)) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339115822996510849141142816742 : (p1 → (p1 ∧ (((((p4 ∧ ((p2 → (p1 ∧ p1)) ∧ (((p1 → (p1 ∨ ((p4 ∨ p5) ∧ p5))) → p5) → p3))) ∨ p2) → False) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48321336642335188415719277962 : (((p1 ∨ ((((p4 ∧ p2) → p2) ∧ (p5 ∨ (True ∧ (p3 ∧ (((p5 ∧ ((False → p1) ∧ p2)) → p4) ∨ p4))))) ∧ p4)) → (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161665664404506433131702398351 : ((p1 ∨ (p2 ∧ ((((p2 → (p2 → p2)) ∧ p5) ∧ p4) ∧ (p2 ∨ (((p1 ∧ False) → p4) ∨ p4))))) → ((False ∧ p2) ∨ ((False ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336060659956591165927615817582 : (p1 → ((p5 → (((p4 ∧ ((p4 ∨ p3) ∨ ((p3 ∨ p5) ∨ p5))) ∧ ((p5 → ((p1 → (p5 ∨ p2)) ∧ p3)) ∧ (True ∧ p3))) ∨ p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143362834945955232951068927166 : ((p4 → (p5 → (p4 ∧ (True ∨ ((True ∨ (((False ∧ p4) → True) ∨ False)) ∨ ((p1 ∧ (p2 ∨ p5)) ∨ (True ∧ p2))))))) → ((p1 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657881592452590511352559869335 : ((((False ∧ (p5 → (((p1 ∨ ((p3 → False) ∧ ((p3 ∧ ((True ∧ p4) ∨ p4)) → p5))) ∧ (p2 ∧ True)) ∧ (False ∧ p4)))) ∨ (True ∨ False)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_172243336144705617654728033456 : ((((False ∨ (p5 ∨ p1)) ∨ (p1 ∧ (p2 ∨ p5))) ∧ (p1 → (False ∧ (True → p4)))) ∨ (p3 ∨ ((p3 ∨ True) ∨ ((p4 ∧ (p4 → p4)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62080254956545272971670135647 : ((p2 ∧ (p2 ∧ ((((((((p2 ∨ (p1 ∧ (True → ((p2 → False) ∧ p3)))) ∨ True) → p4) ∧ p4) ∨ (p2 ∧ p5)) ∧ p3) ∧ p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_989569289785718016010240232943 : (((p3 ∧ ((p3 ∧ (True → False)) ∧ (p3 → ((True ∨ p2) → (((p1 → (p3 → True)) → (p1 ∨ (False ∨ (p4 ∨ (True ∧ p2))))) → p2))))) → p1) ∧ True) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226319182086352194006958151264 : (((p5 ∨ False) ∨ p4) ∨ (True ∧ ((((False ∨ (p4 → p3)) ∧ p1) ∨ False) ∨ ((((p2 ∧ p2) → (p1 ∧ ((False ∧ p1) ∨ p1))) ∧ False) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_44524851490057908512033410472 : ((((p5 ∨ ((((p1 → p3) ∨ p5) ∧ (p2 ∧ p5)) → p1)) ∨ ((((p3 ∧ True) → (False ∧ False)) ∨ p5) → ((p1 ∨ p4) → False))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668566374163608242209601136983 : ((((((p4 ∨ (p5 ∧ False)) → (p3 ∨ ((((p1 ∨ p3) ∨ (False ∧ True)) → (p3 ∧ p1)) ∨ (p3 ∧ p4)))) ∧ True) ∨ (False ∧ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46898671102823056420609748689 : (((((p5 → ((p4 ∨ (((p4 ∧ p4) ∧ (p5 → False)) ∨ ((p3 ∧ p3) → (p2 ∨ p1)))) ∨ (p2 ∧ p1))) → p4) ∨ p5) ∨ (False → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



