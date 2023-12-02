variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115277557472891948933414708330 : (((p4 ∨ (False ∧ ((False → ((p1 ∨ p1) ∨ p5)) ∨ p5))) ∨ (((((((p5 ∧ p1) ∨ p3) → p2) ∧ p2) ∧ p3) → p4) ∨ False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37247175264204429828770932144 : ((((True ∧ (p3 ∧ (False ∧ (p5 ∨ ((((p2 → True) ∧ (p1 ∨ (False ∧ True))) ∧ (p4 ∨ p2)) ∨ (p3 ∧ (False ∧ p1))))))) ∧ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689749203105127435681793732154 : (((((p2 ∧ (False ∧ True)) ∨ ((True ∨ (False ∨ True)) → (p5 ∨ (p4 → (False ∧ False))))) ∨ ((p5 ∨ (p4 ∨ ((True ∧ p2) → p2))) ∨ p1)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118653909199313212917385663017 : ((p4 ∨ (p4 ∧ ((((p2 ∧ p4) ∨ p4) → ((p1 ∧ True) ∧ (p2 ∧ (p5 ∧ (p5 ∨ True))))) ∨ (p3 ∧ (p4 ∧ (p5 ∧ p3)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_910503847879811169616826747 : ((p5 → (p3 ∧ (((False ∧ p5) → (((((False ∨ (False ∨ True)) ∧ True) ∨ ((p3 → p2) → p3)) ∨ (p5 ∧ p1)) → p3)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134334334906139278216830760902 : (((p3 ∧ (True ∧ ((((p5 → p2) ∨ (p3 ∨ p5)) ∧ (p5 ∨ ((p5 → (p3 → p2)) → p1))) → (False ∧ p2)))) ∨ True) ∨ ((p3 → False) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54124539220610169328879116045 : (((False ∨ ((p5 ∨ p3) → (p2 ∨ ((p5 ∧ True) ∨ p4)))) → ((p1 ∧ ((p2 ∨ p2) ∧ ((p2 ∧ ((p5 ∧ p4) → p4)) ∨ False))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670248314185552555961741245719 : (((((p5 → ((p3 → p2) ∧ False)) ∨ ((p3 → p5) ∨ ((p5 ∧ False) ∧ (((True ∨ (p5 ∧ p2)) → p5) ∧ p4)))) ∨ ((p4 ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808377692471721745391272652881 : (((p4 → (p1 ∨ ((((p2 ∧ ((True ∧ p1) → p5)) ∧ (p4 → False)) ∨ ((p2 → (False ∨ (True ∨ False))) ∧ (p5 ∧ True))) ∧ (p3 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115431303070195411715717299544 : (((((((p3 ∧ False) ∧ p4) → p1) ∨ p1) → p1) ∨ ((p1 → ((True ∧ p5) ∧ (p3 ∧ ((p2 ∧ (True ∧ p5)) ∨ True)))) ∨ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150549887656540316853583753461 : (((((p4 → p4) ∨ ((True ∧ p4) ∨ p4)) → (((p3 → p2) → (True ∧ p4)) ∧ ((p3 ∧ p4) ∨ False))) ∧ p1) → ((p3 ∧ p3) ∧ (p4 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p4) ∨ ((True ∧ p4) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : ((p4 → p4) ∨ ((True ∧ p4) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h15
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h14
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
  have h24 : ((p4 → p4) ∨ ((True ∧ p4) ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h25
    -- One of the premise coincides with the conclusion.
    exact h25
  -- We have shown the premise of h22, we can now drive its conclusion.
  let h26 := h22 h24
  -- We need to get the right conjuct of h26 based on <expert-advice>.
  let h27 := h26.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h30
  case inr h31 =>
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323999260180226262591334549134 : (p5 ∨ (((p5 ∧ p5) → ((((p3 ∨ True) ∨ p5) ∧ (p3 ∨ (p1 → False))) ∨ p3)) ∨ ((((p3 → (p5 ∧ p4)) ∧ p4) → (p4 ∨ p5)) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722756145395370626902539947805 : (((((p4 → p5) ∧ p1) ∧ (p2 ∧ (p4 ∧ (p5 → (((False → False) → (((p5 → (p2 → (True ∧ True))) ∧ (p2 ∨ p3)) ∧ p4)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300665519880377603015957169203 : (False ∨ (((((((((p1 ∨ p4) ∧ p5) → p3) → p4) ∨ (False → (p4 ∨ False))) ∨ p5) ∨ True) ∨ p2) ∨ (((p5 ∨ p1) ∧ (False ∧ True)) → p2))) := by
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
theorem thm_5_vars_114058379542811389221295406166 : ((((p5 ∨ (p3 ∨ (p3 → (p4 → ((p1 ∨ (p5 ∨ p5)) ∧ p1))))) ∨ ((p1 ∨ p3) ∨ (p3 ∨ True))) ∨ (True → (p3 ∧ p1))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780745555031522023451088328202 : (((p2 ∨ ((p4 ∨ (False ∧ ((p2 ∧ p1) ∧ p2))) ∨ ((((p4 ∧ p4) ∧ (True ∨ p5)) → (True ∨ (p2 → True))) ∨ (p5 ∨ (p3 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156781023959310838348270140804 : (((False ∧ ((((p1 ∧ (False ∨ (p2 → (p1 ∧ (False → p2))))) ∨ (p4 → p5)) ∨ True) ∧ p5)) ∧ p5) ∨ (p3 ∨ (((p4 ∨ True) ∧ False) → False))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135835174310470968515473047307 : ((((True ∧ p2) ∧ (((p3 ∧ p2) ∨ (True ∧ p3)) ∧ (False ∨ False))) ∧ (True → (p2 ∨ ((p3 → (p3 ∨ p5)) ∨ False)))) ∨ (True ∧ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90751683308008872170736550800 : (((p1 ∨ p5) ∧ (((p3 → p1) → ((p4 ∨ p1) → ((((((p2 → p5) ∨ p4) ∧ True) ∧ p4) ∨ p1) ∧ False))) ∨ (False ∧ (True → p5)))) → p5) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p3 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h6
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p4 ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354638151191395944221645298253 : (p5 → (((((((p2 → (True ∧ (p5 ∧ (p4 ∨ True)))) ∧ False) → p4) ∧ (((p1 ∧ (p4 → (p1 ∨ True))) ∨ p3) ∨ True)) ∧ p5) → p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41768670920527943741879739980 : ((((p5 ∧ ((p3 ∨ True) ∨ True)) ∨ (((p5 → False) → (p3 ∧ p2)) ∧ ((p2 ∨ p1) ∨ ((False ∨ p3) ∨ ((True ∧ p2) ∧ p2))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110918225116220313591761897707 : ((((p4 ∨ ((p4 ∧ ((((p3 ∧ p4) ∨ (True ∧ (p3 ∧ (p2 ∧ ((False ∨ True) → p5))))) ∨ True) ∨ p3)) → p3)) → p5) ∧ p1) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58304971912701275737003251398 : (((True ∨ p4) ∧ ((((p5 ∨ (True ∧ p4)) → ((p4 ∧ p1) → (((False ∧ (p5 ∨ p5)) → (p2 ∧ p5)) ∧ (p3 ∧ p5)))) ∨ p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113610811963380155832769346915 : (((p4 ∨ (((((p2 → ((p2 ∧ (True ∨ p3)) ∧ p4)) ∨ (p2 ∨ (p1 ∨ p3))) → (p4 ∨ p5)) ∧ p4) ∨ p3)) ∨ (True → True)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150296595962770742622703080937 : ((p4 → ((((((((p1 ∨ p1) ∧ False) ∧ p2) ∨ p2) ∧ p2) ∧ p2) ∨ (p3 → True)) ∧ (False → (p3 ∧ p3)))) ∨ ((False → p2) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140772069571691335590244277571 : (((((True ∧ ((False → p2) → (p3 ∧ (p4 ∨ True)))) → False) ∧ True) ∧ (p3 ∧ ((p5 → (False ∧ (p2 ∧ p3))) ∨ p2))) → ((p2 ∧ True) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (True ∧ ((False → p2) → (p3 ∧ (p4 ∨ True)))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39996290681725972204673468231 : (((p5 → ((p1 ∨ ((p2 ∧ p1) → (((False ∧ p1) ∧ (p4 ∨ ((False → p2) ∨ (p3 ∨ p2)))) ∧ (p4 ∧ p1)))) → (p4 ∧ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346900085189511372166221501467 : (p3 → (((((((False ∨ p3) ∨ p5) ∨ p5) ∨ ((p4 ∨ ((p5 ∧ False) ∨ p5)) ∨ p1)) → p4) → p1) ∨ (True ∨ (False ∧ (p5 ∧ (p4 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158311711778603282470688309148 : (((True ∨ (True ∧ p3)) → (((p4 ∨ p4) → (False ∨ ((p4 ∧ p3) → (p2 ∨ (p1 → p1))))) ∨ False)) ∨ (p1 ∨ ((p3 → (p3 ∨ False)) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49417788384534659017824815455 : ((((p5 ∨ ((p2 ∧ (((p5 ∧ (((p3 ∧ p5) ∨ p3) → p2)) ∨ ((p5 → p4) → p5)) ∨ p2)) → p1)) ∧ p2) → ((True → p5) ∨ True)) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731606439771168779020214892923 : ((((p1 → (True ∨ p2)) → (((True → (((False ∨ (p5 → ((False ∨ p4) ∧ True))) → ((p3 → p4) ∧ p1)) ∨ (p2 → True))) ∨ False) ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204259639892094317892267859391 : ((((p4 ∧ False) ∨ (p1 → p5)) ∧ True) ∨ ((p2 ∧ ((p3 ∨ ((p5 ∧ p5) → True)) ∨ p5)) → (((p5 ∨ p2) → (False ∨ (False ∧ p3))) → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (p5 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : (p5 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : (p5 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61064799004123615420164265464 : ((False ∧ ((((False ∨ (True ∨ ((p3 ∨ (p3 ∨ (True ∧ p2))) ∧ (True ∨ p3)))) → p2) ∧ (p4 ∨ (p5 ∨ p2))) ∨ (False → (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317030321901112709450292598650 : (p3 ∨ (p4 → (((p4 ∨ (False ∧ p4)) → (((p5 → (False ∧ (p5 ∨ p5))) ∨ p2) → (((p1 ∧ ((True ∧ p3) ∨ p3)) → p5) ∨ True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615697771919251547397422690972 : (((((((False ∨ ((True ∨ True) → False)) → p5) → (p3 ∧ (p2 → (p4 ∨ p3)))) ∧ (p3 ∨ ((False → (p1 ∨ p3)) ∧ (p3 → p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_261603284739478376403369096395 : ((p5 → p4) → (p3 ∨ ((((p1 ∨ True) → ((p1 → False) → p3)) ∨ False) ∨ (((False ∧ (((p1 ∧ p2) ∨ p4) ∧ p4)) → (p5 → False)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199594305208717246313084712491 : ((((((p1 ∧ p4) ∨ True) → False) → True) → False) → (p3 ∨ (((False ∧ p2) ∧ p4) ∧ (((True ∨ (((p3 → p2) ∧ p2) → True)) ∨ p3) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ p4) ∨ True) → False) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721322136581416744279626631379 : (((((p5 → False) → (False ∧ True)) → (p5 ∧ ((False ∨ p1) ∨ (p1 → ((True ∧ p1) ∧ ((p1 ∨ (p1 ∧ (p5 ∨ p4))) ∧ (True ∨ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172997278613886077648923513304 : ((p5 ∧ ((p1 ∧ (p2 → (p4 ∨ ((p1 ∨ p3) ∨ p5)))) ∨ ((False → p1) ∧ p2))) ∨ (((p4 → False) ∧ (p3 ∧ p1)) ∨ ((p1 ∧ p3) → p3))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110761103626360503413133297485 : ((((p1 ∨ ((p2 → (((p2 ∧ p5) ∨ p5) ∧ p1)) → ((True → (p2 ∨ ((p5 → p1) ∧ (p1 ∨ p4)))) ∧ p1))) ∧ p4) ∧ False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622121776029026658693126239337 : ((((p2 ∧ (((p3 ∧ p2) ∨ (((p4 ∨ p1) → True) → (p2 ∨ p5))) ∧ ((p3 ∧ p3) ∨ ((p5 ∧ ((False ∨ True) ∧ p5)) ∧ p1)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_659391818963043896586457497547 : ((((((p2 ∨ (((p5 → False) ∧ p2) ∧ ((p4 → ((p1 ∨ (False ∧ p5)) ∨ ((p4 → True) → False))) ∧ p5))) ∧ p2) ∧ p5) → (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68627776310787915798984212519 : ((p4 → ((p4 ∧ (p4 ∧ ((p3 ∧ ((((p5 ∧ (p1 → (False ∧ p5))) ∨ (p5 ∧ (p4 ∧ True))) → (p1 ∨ p2)) ∨ p3)) ∨ p1))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116613541585107077813383469010 : (((True → p5) ∧ (((False ∨ False) → ((p2 → p2) → (p5 ∧ p4))) → (((p5 → (p3 ∧ p3)) ∨ (True ∨ (p3 ∧ p4))) ∨ True))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206125604610487333220879364788 : ((p4 ∧ ((p2 → p2) ∨ (p5 ∧ p5))) ∨ ((True ∨ (p4 ∨ p2)) → (p1 ∨ ((False ∨ (False → (p4 → ((p5 ∨ (p2 ∧ False)) ∨ p5)))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355605486896343604116344541239 : (p5 → (((p3 ∧ p4) ∨ (((p2 → p5) → False) → ((p5 ∧ p2) ∨ (((p4 ∧ (True → (p5 ∨ (p4 → True)))) → p2) ∧ p1)))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85961610579538554942301507265 : ((((p5 → ((((p1 → p5) → False) → p4) ∨ p2)) → p5) ∧ (p4 → ((p5 → ((p5 → ((False ∧ True) ∧ (p1 → False))) ∨ p1)) ∨ True))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → ((((p1 → p5) → False) → p4) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p1 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589083504280552518867575907808 : (((((p3 → ((False → False) → ((p5 ∧ (p1 ∨ False)) ∨ (p5 ∨ (((p5 → p1) ∨ (p3 ∨ p1)) ∧ ((p4 → p4) ∨ False)))))) ∨ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113143146737140047970372500843 : (((p3 → ((((False ∨ (False ∨ True)) ∧ True) ∧ (((p2 ∧ (True ∨ p2)) ∧ (((p1 → False) → True) → p3)) ∧ False)) ∧ p5)) → p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317811140761635483180770922765 : (p4 ∨ (((p5 ∨ ((p4 ∧ (p3 ∨ p3)) ∨ p3)) ∨ ((p4 ∨ p3) → (p5 → (True ∨ (p1 ∧ ((((p5 → p5) ∨ p1) ∨ False) ∧ p5)))))) ∨ p2)) := by
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
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951632765479486813084496061291 : ((((p1 → (False ∧ p1)) ∧ (((((p3 ∨ p5) → ((p1 ∨ p5) ∧ p2)) ∨ p5) ∧ ((((p1 ∨ p3) ∨ p1) → p3) → p3)) ∨ (p2 ∧ p3))) → p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (((p1 ∨ p3) ∨ p1) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h12 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h11
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h13 := h2 h12
            -- We need to get the left conjuct of h13 based on <expert-advice>.
            let h14 := h13.left
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- We need to get the left conjuct of h18 based on <expert-advice>.
          let h19 := h18.left
          -- False on the left can always be used.
          apply False.elim h19
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h20 := h6 h8
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h22 : (((p1 ∨ p3) ∨ p1) → p3) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h25
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h27 := h2 h26
            -- We need to get the left conjuct of h27 based on <expert-advice>.
            let h28 := h27.left
            -- False on the left can always be used.
            apply False.elim h28
          case inr h29 =>
            -- One of the premise coincides with the conclusion.
            exact h29
        case inr h30 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h31 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h32 := h2 h31
          -- We need to get the left conjuct of h32 based on <expert-advice>.
          let h33 := h32.left
          -- False on the left can always be used.
          apply False.elim h33
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h34 := h6 h22
      -- One of the premise coincides with the conclusion.
      exact h34
  case inr h35 =>
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- One of the premise coincides with the conclusion.
    exact h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339507803321082608720975862015 : (p1 → (False ∨ (((p3 → True) → ((p3 ∧ p4) ∧ False)) ∨ ((p1 ∧ p1) ∨ (True ∧ (p4 → (p5 ∧ (((p3 → (True ∧ p3)) → p4) → p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317007986969569711140587234434 : (p3 ∨ (p3 → ((p1 → p5) ∨ (((False → (((p5 ∧ True) ∨ p4) → p5)) → (p2 ∧ p4)) ∨ ((False ∨ (p1 ∨ (p3 → (False → p5)))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153011687898247980105133546906 : ((p2 ∧ ((p4 ∨ (((p4 ∨ (p4 ∨ True)) ∨ ((p4 ∧ p4) → True)) ∧ ((p1 → p3) → (True ∧ True)))) ∨ False)) → ((p5 ∧ (p4 → p4)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136259820767988278886703557729 : (((((p1 ∧ True) ∨ (p2 ∧ p1)) ∧ p2) → (p1 ∧ (((((p1 ∨ (p5 ∨ p5)) → p5) ∧ p2) → p3) → (p5 ∨ p3)))) ∨ (p4 → (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164610971609419461814523772587 : (((p2 ∧ (((True → ((p4 ∧ p4) → p2)) ∨ (((p1 ∧ p3) ∨ p1) ∨ p4)) ∨ p5)) ∧ p5) ∨ (((p3 ∧ False) ∧ (p5 → (p1 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228242274006953838697181027187 : ((p5 ∧ (True → p4)) ∨ ((p4 ∨ True) → (((p2 ∨ (False → False)) ∧ p3) ∨ ((p4 ∨ True) ∧ (p4 → (p2 → (False ∨ (p1 ∨ (p2 → p2))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42357266043947142506564216766 : (((p3 ∧ (False ∧ ((((p3 ∨ (p1 ∨ (p3 ∨ p4))) → (False → (True ∧ (p3 ∧ False)))) → ((True ∧ p2) → (p2 ∨ True))) → p1))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148895625684234291526311030327 : (((p2 ∧ ((False → p5) ∨ p1)) ∨ (p2 ∨ (((p4 → (p3 ∧ p4)) → p2) → ((p5 ∧ (p2 → p4)) ∨ p5)))) ∨ (((p3 ∧ p1) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747766158756057374377045814513 : ((((False → p1) → ((((p2 ∧ p5) → ((p5 ∨ (True ∧ (False ∨ (p1 ∧ p4)))) ∨ p3)) ∧ p1) ∧ (p1 ∧ ((p2 ∨ p4) ∨ (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820147464891411598725098970837 : (((((((p5 ∧ (p5 → (p4 ∧ p2))) ∧ ((False → p1) ∨ ((p2 ∨ p5) → (p1 ∧ False)))) ∧ p3) ∧ (p4 → ((False ∨ False) ∧ True))) ∧ p2) → p1) ∧ True) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h15 := h11 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h13
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (p2 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- One of the premise coincides with the conclusion.
    exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178414375753258208534832380556 : (((p5 ∧ (True ∨ (False → ((False ∧ (p2 ∧ p2)) ∧ True)))) → (p4 ∧ p5)) ∨ ((((p5 ∧ ((p1 → False) ∧ p2)) → (p4 ∨ True)) ∨ p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641694780251377100043587153334 : (((((p1 ∨ p2) → (p1 ∧ (((True ∧ True) → p1) ∨ (((((p1 → (p2 → False)) ∨ (p2 ∨ p3)) ∧ (p2 ∧ p5)) → True) → p2)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213867362153672878048743803762 : (((p1 ∨ (p3 ∨ p4)) ∨ p2) ∨ (p5 ∨ (p4 → (((True ∧ (p3 → (p5 ∨ (p5 ∨ p3)))) ∨ (((p1 ∧ p4) ∧ p5) ∨ False)) ∨ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300970836363688394055368694401 : (False ∨ (((p3 ∨ p5) ∧ (p2 ∨ ((True ∧ (p1 ∨ (p4 → True))) ∨ p2))) ∨ (p5 → ((((p3 ∧ (p4 ∧ p2)) → (p2 ∨ p5)) → p5) ∧ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168711730268777787756189004641 : ((True ∨ ((((False → (p3 ∨ p3)) → False) → p2) ∨ ((p4 ∧ p1) ∨ (p1 ∨ (True ∨ p3))))) → ((False ∨ ((False ∨ p1) → (p5 → p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h25 =>
            -- False on the left can always be used.
            apply False.elim h25
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h24
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h29
            -- Implications on the right can always be decomposed.
            intro h30
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h31 =>
              -- False on the left can always be used.
              apply False.elim h31
            case inr h32 =>
              -- One of the premise coincides with the conclusion.
              exact h30
          case inr h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h34
            -- Implications on the right can always be decomposed.
            intro h35
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h36 =>
              -- False on the left can always be used.
              apply False.elim h36
            case inr h37 =>
              -- One of the premise coincides with the conclusion.
              exact h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264808964096874346441966685445 : (True ∧ ((p3 ∧ p3) ∨ ((((p1 ∧ (p3 ∨ (((p3 ∨ True) ∧ False) → ((((True ∨ (p2 ∨ p4)) ∨ p2) ∧ p4) ∨ p1)))) → p4) ∧ p4) ∨ True))) := by
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
theorem thm_5_vars_1820978562646851174957944314 : ((p3 → (((p1 ∨ (p2 ∨ p5)) ∨ (p4 → ((p4 → (True → (p5 ∨ (p3 ∧ p4)))) ∧ p4))) ∧ (False ∨ True))) ∨ (p2 ∧ (True ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728991779208716631369965689122 : (((((p2 ∨ p1) ∧ p4) → ((((p2 ∨ (True → True)) → (((p2 ∧ p2) ∧ p4) ∧ True)) → (p3 ∨ (p3 ∧ (p1 → (p5 ∧ False))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215160231885666297060188540154 : ((True ∧ ((p3 → False) ∧ p3)) ∨ ((((((((p1 → p1) ∨ (p4 ∨ p4)) ∧ p4) ∧ ((p5 → (p4 ∨ True)) ∨ p5)) → p2) ∨ p2) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310287626883283364454291767688 : (p2 ∨ (((((p2 ∨ ((False → False) → p3)) → False) ∧ p5) ∧ p2) ∨ (((p5 → False) ∧ (True ∧ p4)) → (p4 ∨ (p1 → ((p1 ∧ p5) ∨ p2)))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_553793715934464422645570494712 : (((p2 ∨ (((p4 → p2) → (False ∧ ((p2 → p3) ∧ (p2 → (p2 ∨ (p3 ∨ ((p1 → p2) → p4))))))) ∨ (True → (p1 ∨ (True ∨ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712673809461549117884285066553 : (((((p2 ∨ p4) ∧ (False ∨ (p3 ∧ p1))) ∨ ((p2 ∨ (p5 → (p3 → ((False → (((True ∨ (p2 ∧ False)) ∨ False) ∨ p5)) ∨ p3)))) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335822733110120404205201217789 : (p1 → (((True ∨ ((((p3 → (p3 ∨ p1)) ∧ False) ∨ (False → ((p3 ∨ p3) ∨ p1))) ∨ (p3 ∨ p5))) → (p3 ∨ (p2 ∨ (p1 → p1)))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213405128678922984927158802832 : (((p1 ∨ (p5 ∨ True)) ∧ p1) ∨ ((True → p5) ∨ ((((True ∨ ((p2 ∨ p1) → True)) ∧ (p4 ∨ (p3 → (p3 ∨ p3)))) ∨ (p5 → p4)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118607362011855001918568274164 : ((p4 ∨ ((((p2 ∧ p4) ∧ False) ∨ ((p4 ∨ (((p2 ∨ p4) ∧ (False → p5)) ∧ p2)) → (p3 ∨ True))) → (p2 ∧ (p4 → p3)))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56586763249552788275474202133 : (((p2 → ((p2 ∧ p2) ∧ p2)) → (((p4 ∧ p4) ∨ True) ∧ ((p2 ∨ (((False ∨ (False ∨ p1)) ∨ p1) ∧ p4)) ∨ ((False → p1) ∧ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751508516144878379021340611881 : (((True ∧ (True ∧ (True → (((True ∧ (True → ((p3 ∧ p4) ∧ p4))) ∧ False) ∨ (((p1 ∨ p2) ∧ (((False ∧ True) → p2) → p1)) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177917239458593996527624405092 : (((((p3 ∧ (p2 ∧ (p5 ∧ p3))) ∧ p4) ∨ (p1 → (True ∧ True))) ∨ p5) ∨ (p2 → (p5 → (((True ∧ p1) ∧ p5) ∨ ((p1 → p4) ∧ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45985694699157850492826024649 : (((((True ∧ ((p5 ∨ ((p4 ∨ (p4 ∧ p4)) → p5)) ∧ (p4 → (((p4 ∨ (p2 ∧ False)) ∨ p5) → p3)))) ∨ p5) ∧ False) ∧ (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245967904302226464461290781181 : ((p4 ∧ True) ∨ ((((True ∨ p1) ∧ p3) ∧ (False ∧ (((False ∨ p3) ∨ (((p5 → p3) ∧ False) ∧ p4)) ∨ p4))) ∨ ((False → (p5 ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53841999182807573627600064848 : ((((p5 ∧ ((p5 ∨ False) ∨ p4)) ∨ (p2 ∨ (p1 ∨ p2))) ∨ ((p3 ∨ (False → True)) ∨ (((p2 ∨ (True → p1)) ∧ True) ∧ (p5 → False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_151910633408118073098541435073 : (((p4 ∨ (((((False → p5) → p5) ∧ p1) → ((p2 ∨ p1) ∧ p5)) ∨ p3)) → ((False → p1) ∧ (False ∨ True))) → ((p5 ∨ (False → False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786974455444629576474520956674 : (((p4 ∨ ((p5 ∧ p3) ∧ ((p2 → ((p1 ∧ ((p4 → ((p5 ∨ p5) ∧ (False → (p4 → True)))) → True)) ∨ ((p5 → p2) ∨ p2))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42805558558636071254675970813 : (((p1 → ((((p1 ∨ (False ∧ (((((True ∧ p2) ∧ p3) ∧ (p1 ∨ p5)) ∧ p4) ∧ (True ∧ p2)))) → p2) → (False ∧ p2)) ∨ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41947775975809713928249847607 : ((((p1 ∧ False) ∧ (p5 → ((((False ∧ p1) ∨ p5) ∨ (((((p5 ∨ False) ∧ True) ∨ (False ∨ (False ∧ p4))) ∧ p4) ∨ True)) ∨ True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777225201941832799866196514021 : (((p1 ∨ ((((((False ∨ ((True → p5) → p3)) ∨ p2) → p1) ∧ (True ∨ p3)) ∧ ((p2 ∧ p4) ∨ (p5 → p5))) ∨ (True → (p5 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354371719918272247336358409006 : (p5 → ((((p2 → (False ∨ (False ∨ p5))) ∨ p1) → (((p2 ∨ ((p1 → ((p4 → p2) ∨ p2)) ∧ (p2 → p1))) ∨ True) ∨ (True ∨ p3))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792325640024748158520109597637 : (((True → (((p2 → (p2 ∧ (False ∨ (p1 ∨ (((p4 ∨ p3) ∨ p4) ∧ p5))))) ∨ (p3 ∧ p2)) → (True ∧ ((p2 ∧ p1) → (p4 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321339638848743429790445628712 : (p4 ∨ (p5 ∨ (p4 ∨ (True → (((p4 ∨ p4) ∨ (p5 → (p5 → ((p4 → True) ∨ p3)))) ∨ (True ∨ (((p5 ∨ (True ∧ p4)) ∧ False) → p2))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43978753773791588670484040979 : ((((((((p3 ∨ p1) → p1) → (((p2 → ((True → True) ∧ ((True ∧ p1) → True))) ∧ False) → False)) ∧ p3) ∧ p3) → (p1 → p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135571157237392376685767499310 : ((((((True → p2) ∨ ((p4 ∨ ((p1 ∨ p3) → p1)) ∧ p3)) ∧ (p2 ∧ p3)) ∧ False) ∨ ((p2 → (p5 ∧ True)) → p2)) ∨ ((True → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597021788765803908993380056400 : ((((((p3 ∨ (p5 ∨ (False ∧ True))) → False) → ((((True → False) ∨ (p1 ∧ p2)) → ((p5 → (False ∨ (p2 → p4))) ∨ p2)) ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219278580002053116574954150954 : ((p1 ∨ (p2 → (p1 → False))) → (p2 ∨ (((True ∧ p1) → (True ∧ ((p3 → (p5 ∨ ((p1 ∧ p5) ∨ True))) → ((p3 → True) → p2)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314977068543782947453657703061 : (p3 ∨ (((p1 ∨ ((False → p5) ∧ (p5 → True))) ∨ p4) ∧ ((p2 → (False ∨ p3)) ∨ (p3 → ((((False ∨ (p1 ∧ p1)) ∧ p2) ∨ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336139965832857567896078914574 : (p1 → (((p4 ∨ (p5 ∨ ((p2 ∨ p2) → (p5 → ((p4 → p2) → ((p2 ∧ ((True ∧ (True ∧ p4)) ∨ p4)) ∨ (p2 → p4))))))) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65260363384754886968753712152 : ((p3 ∨ (((p3 ∧ p4) ∧ (p5 ∨ ((p2 ∧ (p1 → False)) ∨ (p3 ∨ ((p5 → p1) ∨ ((p1 ∧ False) ∧ (p2 ∧ (p4 ∨ p2)))))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51100876214138797369157127269 : (((((p1 ∧ p5) ∨ ((((p1 ∨ (p2 → False)) ∧ ((p5 ∧ False) ∨ p3)) → p2) ∨ False)) ∧ p5) ∨ (False → ((p4 → p1) ∨ (p2 → p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254892525143179841147219642973 : ((p4 ∧ True) → ((((p4 ∧ p3) ∧ ((p3 ∧ ((p4 → True) ∧ (((True → True) ∧ (True ∨ p5)) → p5))) ∨ p5)) ∨ p3) ∨ ((p1 → p4) ∨ p4))) := by
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
theorem thm_5_vars_754677784296840307160902344770 : (((False ∧ (p4 ∧ (False ∨ ((((True ∧ (p2 ∨ (((True → p5) → p2) → (True ∧ p4)))) ∨ p2) → (p1 ∨ (p5 ∧ (True → p2)))) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



