variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180748221948877964746003457238 : ((((True ∨ False) → (p4 ∧ p3)) ∨ (p5 ∧ ((False ∨ (p3 ∧ p3)) ∨ True))) → (((p3 ∨ True) ∧ (p4 ∨ True)) ∧ ((p4 ∧ p1) → (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h22.left
  let h24 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213776837803867587001035594031 : (((False ∧ (True ∨ p1)) ∨ False) ∨ (((p1 → (((p5 ∧ (False → (p2 ∧ p5))) → p5) ∨ p1)) → (((p5 ∧ True) ∧ (p2 ∧ p3)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313925367509805137347932436647 : (p3 ∨ ((((p4 ∨ (p3 ∨ True)) ∨ (p2 ∨ (((p1 → (False ∨ (((p1 → p3) → (p1 → p1)) → p3))) ∨ p1) ∧ p2))) ∧ p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759426281704542092638612879348 : (((p2 ∧ (((True ∨ False) → (((True → p1) → (((False → p4) ∨ (p2 ∨ p5)) → (p1 → (p1 ∨ False)))) ∨ p4)) → ((p2 ∧ p2) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51569410176321629764724707382 : (((p2 ∨ ((False → ((p3 ∨ ((True ∧ (p1 ∨ p3)) ∧ (p2 → p1))) ∨ True)) → (p1 ∨ p5))) → ((((p1 → p4) → False) ∨ p5) ∨ True)) ∨ p2) := by
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
theorem thm_5_vars_615446161751144896033434925737 : (((((((p5 ∧ (((False → p5) ∧ p4) ∨ (p1 ∨ ((p5 ∨ p1) ∧ False)))) ∧ p3) ∧ p3) → ((True ∧ (True → (p1 ∨ p1))) ∨ p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149179833072438845959617656791 : (((False → p2) ∧ ((((p2 → ((((p3 ∧ p3) ∨ p5) ∧ p5) ∧ (p4 ∨ p1))) ∧ (p3 → p2)) ∨ p2) ∨ True)) ∨ (p5 ∧ ((p3 ∧ False) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61113273031069576075219030955 : ((False ∧ (((False ∧ (p5 → p2)) ∧ (((p2 → p3) → (p4 → p5)) → p5)) ∨ ((p5 ∧ (p1 ∧ p1)) ∨ ((p3 → (p3 ∧ p3)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80774516823431251467937030431 : (((p2 → (((p4 ∨ p4) ∨ (((p2 → (p5 → p4)) → p5) ∨ (p5 → ((p1 ∨ True) ∧ p2)))) ∨ (p3 → (p4 ∨ p2)))) → (False ∧ p1)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((p4 ∨ p4) ∨ (((p2 → (p5 → p4)) → p5) ∨ (p5 → ((p1 ∨ True) ∧ p2)))) ∨ (p3 → (p4 ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60754150734863170086062017667 : ((True ∧ ((True ∧ p1) ∧ ((p4 → p3) → (((True ∧ (((p4 ∨ True) ∨ p3) → (p3 ∧ (p4 ∧ ((True ∧ p3) ∧ p2))))) ∧ p2) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160784601710383338711074360606 : ((((p3 ∧ (p1 ∧ (p4 → False))) ∧ p2) ∨ ((((True ∨ (p5 ∨ p4)) ∨ (p2 ∨ True)) → p3) ∨ p5)) → (p5 ∨ ((p1 → (p4 ∨ p3)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : ((True ∨ (p5 ∨ p4)) ∨ (p2 ∨ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705376336351370653898442834194 : ((((((p1 ∧ p1) ∧ (p3 ∨ (True ∨ p5))) ∨ p1) ∧ ((p3 ∧ p3) ∧ (p4 → ((((True ∧ p4) ∧ True) ∨ ((p5 ∨ p3) ∧ p4)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44428398034387941952190615915 : (((((p1 ∨ (p2 ∨ ((p3 → (p1 ∧ True)) → (p5 → p4)))) → p3) ∧ (p2 ∨ ((False → ((p1 → (True ∧ p1)) → p1)) ∧ True))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310395977740096921328422568859 : (p2 ∨ ((((True → False) ∨ p4) ∨ (p3 ∧ (False ∧ p5))) ∨ (False → (p5 ∧ (p5 → (((p4 → ((p2 ∨ True) ∨ (p2 ∨ p3))) ∨ p1) ∨ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234704738614988178820152680019 : ((p4 → (p1 ∨ True)) → ((((p1 ∧ p4) → p2) → p1) ∨ (((p3 ∨ (p3 → (p4 → (False ∨ p4)))) ∧ (True → True)) ∨ (p3 ∧ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208596026268951945728893179254 : (((p2 → p5) → (p2 → (p3 ∨ p2))) → ((((p4 ∧ p2) ∨ ((p3 → p5) → False)) ∨ (True ∧ True)) ∨ (((False → True) → (p1 ∧ p1)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38476514114959645373686961406 : ((((((p5 ∧ True) → (p4 → ((p1 → False) → (p4 → True)))) → p1) ∧ (((True → (p4 → True)) ∧ (p1 → p2)) ∨ (p3 ∧ False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135588068568264903265887910055 : ((((True ∧ ((p3 → (False ∨ ((p5 ∨ p5) ∧ (False ∧ False)))) ∧ p3)) ∨ (p1 ∨ p2)) ∨ (p5 → (p2 → (p4 ∨ p5)))) ∨ ((True ∧ p5) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50548469444962776187829998902 : (((((True ∨ p2) → (p5 ∨ ((p3 ∧ ((False ∧ ((p4 → p1) ∨ p2)) ∧ False)) ∨ (p1 ∨ p2)))) ∨ p2) → ((p3 ∨ p2) ∧ (False ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52883943637862598941408818698 : (((p1 ∨ ((False ∧ ((True ∧ p1) ∨ ((p3 ∨ (p5 → p3)) ∧ False))) ∨ p2)) → (((p5 → p1) ∧ ((False → (p3 ∨ True)) ∨ False)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68359014729927590635137370085 : ((p3 → ((p3 ∧ ((False → (True ∧ True)) → (p1 ∧ p1))) ∨ ((True → (((p4 → (((p2 ∨ True) ∨ p5) ∨ p3)) ∨ p1) ∧ False)) → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354602584300577172920945769262 : (p5 → (((((p1 → (p3 → (((p1 → False) ∧ p2) → False))) ∧ (p4 ∨ ((p1 ∨ p4) ∨ (p4 ∧ (False ∧ (True ∧ True)))))) ∨ p1) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95540917011049042056582842963 : ((p5 ∧ ((p5 ∧ ((p2 ∨ ((((((True ∧ False) ∨ p1) → p4) ∧ (p3 ∨ p3)) → (p1 ∨ p1)) ∨ (p5 ∨ p5))) ∨ p4)) → (p5 → False))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∧ ((p2 ∨ ((((((True ∧ False) ∨ p1) → p4) ∧ (p3 ∨ p3)) → (p1 ∨ p1)) ∨ (p5 ∨ p5))) ∨ p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149551765213396094905434176116 : ((p2 ∧ (((True → (True → ((((p4 ∧ p3) ∨ p4) → p1) → p1))) ∨ p3) ∨ ((True ∧ False) ∧ (True → p4)))) ∨ ((p4 ∨ (p2 → True)) ∨ p3)) := by
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
theorem thm_5_vars_68918411840386948242332827744 : ((p4 → (p1 ∨ ((p4 → p5) ∧ ((False → True) → (p5 ∨ (((p5 → p4) ∧ (((False → p3) ∧ (p1 → p5)) ∧ (p4 → p4))) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197963435737847170086503803531 : (((p5 ∧ p2) ∧ (p1 ∧ (p2 ∨ (p5 ∧ p3)))) ∨ (p4 ∨ (((p3 ∧ (((False ∧ True) ∧ (p4 ∨ p4)) → p1)) ∨ (p2 → p2)) ∨ (p5 → p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37848052991575871584084960163 : ((((True → ((((p5 ∨ ((False ∨ (True ∧ (p2 ∨ (p2 ∧ (False ∨ p1))))) → p4)) → (False → p3)) ∨ p3) → (p4 ∨ p4))) → p1) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154222283690102456642523632746 : (((((((p3 ∨ p5) ∨ p2) ∨ False) ∨ (False ∨ (p2 ∨ p2))) ∨ (p3 → (False ∧ (p3 ∨ p1)))) ∨ True) ∧ (p3 → (p1 ∨ ((p2 ∨ True) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_303327450850126628152586328592 : (p1 ∨ ((((((True → (p3 ∨ False)) ∧ ((p1 → ((p1 ∧ False) ∧ p3)) ∨ False)) ∨ (((True → (p1 ∨ p2)) → False) ∨ p2)) → p4) ∨ True) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_872508673612581392682930370764 : ((((True → ((((((p5 ∨ ((p5 → False) ∨ p1)) ∧ p4) ∧ p1) ∧ True) ∧ p5) → ((p2 ∨ p2) ∨ (p5 ∨ (False ∧ (True ∧ p4)))))) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → ((((((p5 ∨ ((p5 → False) ∨ p1)) ∧ p4) ∧ p1) ∧ True) ∧ p5) → ((p2 ∨ p2) ∨ (p5 ∨ (False ∧ (True ∧ p4)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h2
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58274752807038862758254187569 : (((p5 ∧ p5) ∧ (False ∨ (((p3 → (False ∨ ((p1 → (((p1 ∧ (False ∨ p2)) ∨ p5) ∧ (p2 ∨ p5))) ∨ (p4 ∨ p3)))) ∨ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173183085045619937641672213902 : ((p4 ∨ ((True ∨ p2) ∧ ((((p4 → ((p4 → p3) → True)) → p3) ∧ p3) → p5))) ∨ ((p4 ∧ (((p3 → p1) → p1) ∧ p5)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322487611068720553451118496800 : (p5 ∨ (((p3 ∨ p5) ∨ (p3 ∧ (((p2 ∧ (p4 ∨ True)) ∧ (p5 ∧ (((p5 ∨ p5) ∧ p2) ∧ (False ∨ ((p4 → p1) ∨ p5))))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160092111230871132531054137815 : (((p4 ∨ ((p2 ∨ (p2 ∧ (((p4 → p2) ∨ (p4 ∧ (p2 ∨ p2))) → (p3 ∨ False)))) → p4)) → p2) → ((p2 → p5) ∨ (True ∨ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310570615503041903078809115622 : (p2 ∨ ((((False ∧ p5) ∨ p3) → True) ∧ ((((p3 ∨ (False ∧ ((False → (p4 ∨ False)) → (p4 ∧ p4)))) ∨ True) ∨ False) ∨ ((p2 → p4) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172906612575318003100952662062 : ((p2 ∧ (((p5 ∧ False) ∨ (p3 ∧ (p4 → (p5 ∧ p5)))) ∧ ((p1 ∨ False) ∨ p1))) ∨ (((True ∨ p3) ∨ (p4 → (p3 ∨ (p3 ∧ p5)))) ∨ p3)) := by
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
theorem thm_5_vars_121621755197673483077980801022 : (((((((p1 ∧ (p2 → (p4 → p1))) ∨ p5) → (False ∨ ((True ∨ p3) ∧ False))) → p2) ∨ (False → (p3 ∨ (p2 ∧ True)))) → False) → (p4 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∧ (p2 → (p4 → p1))) ∨ p5) → (False ∨ ((True ∨ p3) ∧ False))) → p2) ∨ (False → (p3 ∨ (p2 ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((((p1 ∧ (p2 → (p4 → p1))) ∨ p5) → (False ∨ ((True ∨ p3) ∧ False))) → p2) ∨ (False → (p3 ∨ (p2 ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256931840296474276461627129769 : ((p1 ∨ p4) → (p2 → ((p2 ∧ (((p4 ∧ (p1 ∧ (p3 → False))) ∧ False) ∧ (p5 ∨ (p4 ∧ (p4 ∧ p2))))) ∨ (p3 ∨ (False → (p1 ∧ p3)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260064313719236482155754571590 : ((p2 → False) → (((p1 → p2) ∨ ((p4 ∧ p5) ∨ (True → p5))) ∨ ((False → ((False → p1) → p5)) → (((False → p1) ∨ (True ∧ p2)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40530177583051531991475770365 : ((((p1 ∨ ((((((p2 ∧ True) ∨ p5) → (p3 → (p1 → p5))) → p4) ∨ (p2 ∨ p4)) ∧ (p2 → ((False ∨ p1) ∨ p2)))) ∨ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46917810606044789640692073660 : ((((((p2 ∨ ((p5 ∧ p2) ∧ False)) → p1) ∧ (((True ∧ ((p5 → False) → False)) ∧ (True → p1)) ∧ (p1 ∧ p2))) ∨ p2) ∨ (p2 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60882027460443627983288276281 : ((True ∧ (p1 → (p5 ∨ ((p4 → ((((True ∨ (p2 → False)) ∧ (p2 → (p4 ∨ p4))) ∧ p1) → ((p2 ∧ p4) ∧ p4))) ∧ (p1 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10583206009643747638995305259 : (((p4 → ((p4 ∨ False) ∧ ((((True ∨ (p1 → (p4 ∧ (p5 → False)))) → True) ∨ p1) → ((p4 → False) ∨ ((p1 ∨ p2) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_895359681458181552991145278 : ((p3 → ((p5 ∨ ((True → (p4 ∨ ((p3 → False) → (p3 → ((False ∧ (p2 ∧ (p5 ∨ p1))) ∧ (p3 ∧ False)))))) ∨ True)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193922201744772130562377781091 : ((p1 ∨ ((p3 → p5) → (((False → p4) ∧ False) → True))) → (p3 ∨ (((p3 ∧ p5) ∧ (p5 ∧ (p3 ∧ p4))) ∨ (True → (p5 → (p3 ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207629659747267478363621275204 : ((((p2 → (p2 ∧ False)) → p4) → p5) → (p2 → ((p4 ∧ (False → ((((p3 ∧ False) ∨ False) → (p1 ∨ False)) → p2))) → ((p2 → p1) → p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149818559517952815661201587078 : ((p1 ∨ ((((((False → (True → p1)) → True) ∨ p1) → p1) → (p2 ∨ ((p5 ∧ (p1 → True)) → p1))) ∨ False)) ∨ (p3 ∧ (True → (p4 → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((False → (True → p1)) → True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668813588735344117585123244319 : ((((((p1 ∧ ((p1 ∧ True) ∧ ((True ∧ (p5 ∨ (p5 ∨ False))) ∧ p3))) ∨ ((p2 ∨ (p1 → p4)) → p1)) ∨ False) ∨ (p2 ∨ (True ∧ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158053580778533221010518224612 : (((True ∧ (((p3 → p5) ∧ p2) ∧ True)) ∨ (p3 → (p2 → ((p1 → p4) ∨ (p5 → (p3 → p1)))))) ∨ (p5 → (((p3 ∨ p3) ∨ p5) ∨ p4))) := by
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
theorem thm_5_vars_173342754984208617477031553617 : ((p2 → (p1 → (False ∨ (True ∧ (((p5 ∧ False) ∧ False) ∧ ((p4 ∨ p2) ∨ p5)))))) ∨ (p5 ∨ ((p4 ∧ ((p2 → p2) → p5)) → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230022393026205066089652881565 : (((p1 ∧ p1) ∧ p1) → ((p4 ∨ p1) → (((((p4 → p4) ∧ (p3 → ((False ∧ True) ∧ (p5 ∨ (p4 ∨ (p3 → p5)))))) ∨ p2) ∨ p2) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51407442475946753140380639385 : ((((((p2 → p4) → (p3 ∨ ((True ∨ False) ∧ (p2 → p1)))) → (p4 ∧ (p2 → p3))) → p5) → ((((False → True) ∧ p2) → p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193342089548893466267679124418 : ((((p5 ∨ p2) ∨ p4) → (p4 → ((p2 → False) ∨ p2))) → (((p1 ∨ p3) ∨ p4) → ((p2 ∨ p1) ∨ (True ∨ (False ∧ ((False → p4) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
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
theorem thm_5_vars_671120181903360112737050474587 : ((((p1 ∨ ((p3 → True) ∧ ((((p1 ∨ ((p5 ∨ False) ∨ p2)) ∧ (False ∧ False)) ∨ (False ∨ False)) ∧ (p2 ∨ True)))) ∨ ((p4 ∧ False) → p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341693060965391953904636693163 : (p2 → (((((((p4 → (((p1 → p1) ∧ p3) → p4)) → p3) ∨ (p5 ∨ (False → (p5 ∨ False)))) ∨ p5) ∧ False) ∨ (p2 → True)) ∨ (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55691372422824046798199256327 : (((((False ∨ False) → p4) ∨ p5) ∧ ((((p4 ∨ False) → ((True ∨ (False ∨ False)) ∨ True)) → (p1 → (((p1 → False) ∧ p2) ∨ p5))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793173207885739939346943413188 : (((True → (False ∧ ((((p5 ∨ ((p5 ∧ p5) ∧ (((p4 ∨ (p4 ∧ (p1 ∧ (p3 → p4)))) → (p1 ∧ p1)) → p5))) ∧ True) → p1) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193192566915792800362203472128 : ((((p5 ∨ p4) ∨ (p2 ∧ False)) → (p2 → (p3 ∨ False))) → ((((p3 → (True ∧ p2)) ∨ False) ∨ True) → ((p2 → p1) ∨ (p3 → (p3 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655824262212076158611946774602 : (((((((p3 ∧ ((p4 ∧ (p5 ∧ (p3 ∨ p3))) → ((p4 ∧ p4) ∧ (p5 ∨ p2)))) ∨ p4) ∨ p1) → ((p4 → p1) ∧ p2)) ∨ (True ∨ p2)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_621891511438422349605704350743 : ((((p1 ∧ ((p5 ∨ False) ∧ (((p3 ∧ ((p2 → p5) ∨ (p4 → p3))) ∧ (p1 ∧ ((p3 ∧ (p2 ∨ p4)) ∧ (p3 ∨ True)))) ∨ False))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185678297516850856467689481352 : ((p1 → ((p3 → (p5 → (p1 ∨ (True ∨ p4)))) → (p4 → p3))) ∨ (p4 → (((p2 → (False → p5)) ∧ (False → ((p2 → False) ∨ p2))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338548515208015583888459916919 : (p1 → ((False ∨ (p1 → p4)) ∨ ((p4 → (p4 → (False ∨ p3))) ∨ ((True ∨ (((p5 ∨ p2) → p4) → False)) → (((False → False) → p1) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341690562622592169449883112224 : (p2 → (((((((True ∨ True) → (p3 ∨ ((p1 → (p5 ∨ (p1 ∨ (p5 ∧ p4)))) → p4))) → True) → p4) → p5) ∧ (p4 ∨ p4)) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244417507672176466075367122937 : ((False ∧ p1) ∨ (p4 ∨ (((False ∨ p4) ∧ ((p1 → (p4 ∧ ((True → (p4 → False)) → True))) ∧ (p2 ∧ p1))) ∨ (p3 → (p3 ∧ (True ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786437592598773374834288499702 : (((p4 ∨ (((((((False ∨ False) ∧ p3) ∧ (p4 ∨ True)) ∨ (False ∧ p4)) ∨ True) ∨ p1) → ((((p4 ∨ p2) → False) → (p1 ∧ True)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58982454195237290420722231223 : (((p2 ∧ p5) ∨ ((p4 ∨ False) ∨ ((p5 ∨ ((((True → p2) → (p2 ∧ True)) ∨ p3) ∧ ((True ∨ False) → p4))) ∨ (p2 → (p4 → p4))))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322539410156951947704002594147 : (p5 ∨ ((p5 ∧ (((((p3 ∧ ((True ∨ p1) ∧ False)) → (p3 ∧ p5)) → p5) ∨ (False → (p1 → p4))) ∧ (((p4 ∨ p3) → True) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64787587932243826431176294571 : ((p2 ∨ (((p5 ∨ (((p2 → False) → True) → (((p1 → ((False → p1) → p4)) ∨ p2) → p3))) → (p2 → (False ∧ (True ∧ p4)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255244642729573547723839909827 : ((p4 ∧ p5) → ((p1 ∨ ((p5 → (((p3 ∨ p2) → ((p4 ∧ ((p5 → False) ∧ ((p4 → False) ∨ (True → p4)))) ∧ p5)) ∧ p2)) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_330318161637801297193566425037 : (True → (p1 ∨ ((((False ∨ True) → (((p2 ∧ (p4 ∧ p4)) → False) ∧ p3)) ∨ p1) ∨ ((False ∧ (p5 → p4)) ∨ ((False ∧ (p3 ∨ p4)) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329116131202055840031101267601 : (True → (((p2 ∨ False) ∧ (p5 ∧ False)) ∨ ((p5 ∧ (p4 → False)) ∨ ((False → True) ∧ (True → (((True ∧ (p5 ∨ (False → p2))) ∧ p3) → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699466376811286510982904239745 : (((((((True ∨ ((p3 ∨ p3) ∧ p4)) ∨ p5) ∨ (p1 → p1)) ∨ False) → ((p4 → ((((p1 ∨ (False → p4)) ∨ p4) → False) ∨ p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184163073440331814037739572756 : (((p5 ∨ ((p4 ∧ ((False → (p4 ∨ p2)) → p2)) ∨ p5)) ∨ p4) ∨ (p5 → ((True ∧ (p4 ∨ ((p5 ∨ (p3 → p4)) ∨ (p2 ∨ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205126477715746397295708496350 : ((((True ∧ False) → False) ∧ (p4 ∧ p3)) ∨ ((((False → (((p2 → p5) → (True ∧ p1)) ∧ p1)) ∧ ((p3 ∨ p4) → p2)) ∨ p4) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51133259505407731419407582418 : ((((p1 → ((p2 ∧ (((p2 ∧ p1) ∧ p5) → ((p3 ∨ p4) ∧ (True → p2)))) → p3)) ∨ p1) ∨ (p2 ∨ (p2 → ((p2 ∧ p4) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807128917954568884610545641339 : (((p4 → ((((p4 ∧ (p3 ∨ p4)) ∧ ((p1 → p5) ∨ p4)) ∨ (True → (p3 ∨ ((p1 → False) ∧ p2)))) → (True ∧ (False ∨ (True → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130700259208426282891343808598 : ((((p1 → p5) ∨ (p4 ∧ (((p3 ∧ ((p4 ∧ (p3 ∨ p5)) ∧ True)) ∨ True) ∧ p2))) → ((p1 ∨ p3) ∨ (p1 → p1))) ∧ (p5 → (p5 ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215098660431940532317041853256 : (((p1 → False) → (p5 → p1)) ∨ ((((p5 ∨ p1) ∧ p3) ∧ (p4 ∧ (p4 → p3))) → (((False ∨ (True → ((p4 ∨ p4) ∧ False))) ∧ p5) ∨ p3))) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198726183208265376802113976976 : ((p5 ∨ (p1 ∧ ((p2 → (p3 ∧ p5)) → p4))) ∨ (((p3 ∨ p1) → p2) → (((p1 ∨ True) ∨ p3) ∨ ((p5 → ((p2 ∨ p2) ∨ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113650825583821551178862786658 : ((((((p2 ∧ p2) ∧ (True → p2)) ∨ (((p2 ∧ ((p5 → p3) ∨ ((p5 ∧ p3) ∨ False))) → False) ∨ p5)) ∧ True) → (p3 ∨ p4)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68270227362929883442229744671 : ((p3 → ((False ∨ ((p2 ∧ True) ∨ ((p2 ∧ (p5 → (((p1 → True) → False) ∧ False))) ∧ (p1 → ((True → True) ∨ False))))) ∨ (True ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354177240799299382519986727852 : (p5 → (((((p4 → (((p1 → (p4 ∨ (p5 → (p1 ∨ p1)))) ∨ (p1 ∨ p2)) ∧ p4)) → (((p1 ∧ p1) ∧ p3) ∧ True)) ∨ False) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1486149738880910826334259289 : (((False ∨ ((p1 ∧ (p4 → (p4 ∧ (((p3 → (p4 ∨ (p4 ∨ False))) ∧ p3) ∨ True)))) → (p1 → (p1 ∧ p1)))) → p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164798249343634334569515595328 : ((((p3 ∧ (p5 ∧ p3)) ∧ ((p5 ∨ ((((p1 ∧ p1) ∨ p1) ∨ p4) → p5)) → p4)) ∨ True) ∨ (((p1 → ((False ∨ p1) → p1)) → p4) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233657766225693159834569680689 : ((p2 ∨ (p3 ∨ p5)) → ((((p5 → True) → p2) ∧ ((p2 ∧ False) ∨ ((p4 ∨ p4) ∨ ((True ∧ ((p1 ∧ p4) ∧ (p3 → p2))) ∧ p1)))) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h14 : (p5 → True) := by
              -- Implications on the right can always be decomposed.
              intro h15
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h16 := h3 h14
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h18 : (p5 → True) := by
              -- Implications on the right can always be decomposed.
              intro h19
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h20 := h3 h18
            -- One of the premise coincides with the conclusion.
            exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h25 : (p5 → True) := by
              -- Implications on the right can always be decomposed.
              intro h26
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h27 := h3 h25
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h28 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h29 : (p5 → True) := by
              -- Implications on the right can always be decomposed.
              intro h30
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h31 := h3 h29
            -- One of the premise coincides with the conclusion.
            exact h31
    case inr h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h33.left
      let h36 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
          have h44 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h43
          -- We have shown the premise of h38, we can now drive its conclusion.
          let h45 := h38 h44
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h46 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h47 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h48
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h49 := h3 h47
          -- One of the premise coincides with the conclusion.
          exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112847514180817633596648675047 : (((((p4 → p4) → False) ∧ (((p4 → (p3 ∧ (True ∨ (p2 ∧ p1)))) → p1) → (p1 ∧ ((p3 ∨ p4) ∧ (p4 ∧ False))))) → p2) ∨ (p1 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644132073607523234298651544199 : ((((True ∨ (p3 ∧ ((p2 → ((p5 ∧ ((True → ((((p1 ∧ True) → (p2 ∧ p4)) ∧ p5) → (True ∧ p2))) ∧ p2)) ∧ p5)) ∨ p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326870954617791180554968433631 : (True → ((((((True ∨ (p2 ∧ (p3 ∨ (p3 → ((p4 → True) ∧ (p5 ∨ (p2 ∧ False))))))) → (p2 → False)) ∨ True) ∨ (p5 ∨ False)) ∨ p3) ∨ p4)) := by
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
theorem thm_5_vars_42053154890555002284708273292 : ((((p1 ∨ p5) ∨ (p3 ∧ (((((p2 → p4) ∧ p5) → ((p4 ∧ p4) ∨ p4)) ∧ False) ∨ (((p1 ∨ p1) → p2) → (True → p4))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148794534819040331738335537490 : (((p3 → (((p3 ∧ True) ∨ p3) → False)) ∨ (p4 ∧ (((p2 → p2) ∨ p4) ∧ ((p4 ∨ p2) ∧ (p1 → True))))) ∨ ((p3 ∧ False) → (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692342927057035222755464732684 : (((((((p4 → (p3 ∨ (True ∨ p2))) ∧ p3) ∧ (p1 ∧ (False → p3))) → p2) ∧ (((p4 → (p4 ∧ p5)) ∨ ((p1 ∨ p5) ∧ True)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328157635600643019247284943256 : (True → (((((False ∨ (p1 ∨ (p4 ∨ p5))) ∧ ((((p4 → (p3 ∧ (p1 ∧ p2))) ∨ p2) ∧ p5) → p4)) → False) ∧ p3) → ((True → False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60738373231389812056663831938 : ((True ∧ (((p5 → p5) → p5) ∧ ((p3 ∧ p4) → (((p2 ∨ (p5 → ((p2 ∧ ((False ∧ p4) ∨ p2)) ∧ (False ∧ p1)))) ∨ False) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113573372309139312896327025548 : (((True ∧ ((False ∨ ((((p5 ∧ (p3 ∧ p3)) ∨ p3) ∨ ((p3 → (False ∨ p4)) ∨ (p2 → True))) ∨ False)) ∧ True)) ∨ (p1 ∨ p4)) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231317667239187089256419533115 : (((True → False) ∨ p4) → (((True → (False ∨ (p2 → (p3 ∨ p4)))) → (p4 ∧ ((p4 ∧ p2) ∧ ((p4 ∧ ((p1 ∧ False) → p2)) ∨ p4)))) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166459516553363549788726156876 : ((p2 ∨ ((p4 ∧ p5) ∨ ((p1 ∧ p1) ∧ (((p4 ∧ True) ∨ (p3 ∨ (p3 ∨ p5))) ∨ p5)))) ∨ (p5 → ((p5 ∨ (p4 → p1)) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_165579802385978611586243384340 : ((((p5 ∨ p1) ∨ (p3 ∨ ((p3 ∧ p3) ∨ False))) ∨ (((p3 ∧ False) → p1) ∨ (p5 ∧ False))) ∨ ((p4 → p4) → ((p1 → p5) ∧ (p3 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_750842456556097107587089233494 : (((True ∧ ((((True → (False ∨ p4)) → True) → (p2 → (p2 ∧ p4))) ∨ (((p2 ∨ (False → True)) → p4) → (p4 ∨ (p3 ∨ (p3 ∧ p1)))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (False → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689064178392711735075013742694 : ((((((p2 ∧ p1) ∨ (((((p4 → (p1 ∨ p2)) ∨ p4) → p5) ∨ p5) ∨ p2)) ∨ p1) ∨ ((False ∨ p4) ∨ (p1 ∨ ((p4 ∧ p3) → True)))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612105668643353897131336663824 : ((((((p2 → (p4 ∧ (((False ∧ (True ∨ p1)) ∨ (p3 ∨ ((p5 ∨ p4) → p2))) ∧ p2))) ∧ ((p1 → True) → p1)) ∧ (True ∧ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



