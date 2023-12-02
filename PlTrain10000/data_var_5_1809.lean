variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135651655621297309531608662651 : ((((p2 → ((p1 → p4) ∧ (p1 → p4))) → ((p2 ∨ ((p2 → p2) ∧ p5)) ∨ p1)) → ((p1 ∨ p2) ∨ (p4 ∨ p2))) ∨ (False → (False ∧ True))) := by
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
theorem thm_5_vars_177705356260514879033583023748 : (((((p1 → False) → (p1 ∧ (False ∨ (p4 ∧ p4)))) → (p1 ∧ False)) ∧ p2) ∨ ((((p3 ∨ (False ∧ (p3 → p2))) ∧ p1) ∧ (p3 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190190339262180710790677956254 : (((p1 ∨ ((False ∨ ((True → False) ∧ p2)) ∨ False)) ∧ False) ∨ ((((p1 → p2) → p1) ∧ ((True → p2) ∧ p3)) → (((p4 ∧ p3) ∧ p5) ∨ p1))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p1 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52244345320675565513666628159 : (((p5 ∧ (p3 ∨ (((p4 ∨ p3) ∧ ((p4 ∨ p1) → ((True ∧ True) ∨ p4))) ∨ False))) → (((((p1 → p1) ∨ p4) → p2) ∧ p2) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47463624135023360773391823605 : (((p5 ∧ ((((True ∨ (p4 ∨ ((p4 ∧ (p4 ∧ p2)) ∧ p5))) → p4) ∨ (p3 ∨ (p2 → ((False → p5) ∨ p4)))) → p1)) ∨ (False ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65319091598309614117550366849 : ((p3 ∨ ((p4 ∨ (p1 ∨ (False ∧ (((((False ∧ (p4 ∨ p3)) ∨ True) ∧ (p5 → p4)) → p1) ∧ (p3 ∧ True))))) ∨ ((True ∨ p1) ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_698205272395902919058822509189 : (((((((p2 → p2) ∨ p5) ∨ ((False → True) → (p5 → p4))) → p2) ∨ ((False ∨ (p1 ∨ p5)) ∧ ((p1 → (p1 ∧ p1)) ∧ (p5 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667437030968243784410931844852 : (((((False → p4) → (((p3 ∧ p3) ∨ (((((True ∨ (True ∧ p5)) → (p5 → p5)) ∨ p2) ∨ p5) → p4)) ∨ p4)) ∧ (False ∧ (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208257771483816366485485406700 : (((p4 ∧ p3) ∧ (p5 ∨ (p2 ∨ p5))) → ((False ∨ p2) ∨ (((True ∧ (p4 → (p3 ∨ p2))) ∧ ((p2 → True) → p3)) → ((p2 ∨ p5) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66593261279501513979453333792 : ((True → (((p5 ∨ True) → ((((False ∨ p4) ∨ (False → p5)) → (False ∨ ((p5 ∨ True) ∧ p1))) ∧ (p1 → p2))) ∨ ((True ∨ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344770757791832566350899388331 : (p2 → (p4 → ((((((p3 → (p4 → (False → (False ∧ p2)))) ∧ (p4 ∧ (((p4 ∨ False) ∨ False) ∨ p5))) ∨ (p3 → p2)) → p5) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50411278859437280648163541420 : (((p1 ∧ (((((p1 ∧ (p5 ∨ p3)) ∨ False) ∨ ((p4 → p1) ∧ (p3 → (p2 → p4)))) ∨ p5) ∧ p1)) ∨ (((p1 → p2) ∨ False) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742218880997421600630966718806 : ((((p1 → False) ∨ ((((p5 ∧ (p5 ∨ True)) → p1) ∧ (p3 → (p4 ∨ False))) → ((((p2 ∧ p4) ∨ (False ∧ False)) ∨ p3) ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248716211283242811707765869309 : ((p3 ∨ p2) ∨ ((True ∧ p1) ∨ ((((((p2 ∨ (p2 → p3)) ∨ p5) → False) ∨ ((True ∧ (p3 → (p3 ∨ (False ∨ False)))) ∧ True)) → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ (p2 → p3)) ∨ p5) → False) ∨ ((True ∧ (p3 → (p3 ∨ (False ∨ False)))) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208131285528644904246490516880 : ((((p2 → p1) ∨ True) → (p5 → p3)) → (((False ∨ True) ∧ (p1 ∨ ((True → (p3 ∧ p5)) ∧ p5))) ∨ ((False ∧ ((False → p1) → True)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_113210968372133183835494368655 : ((((((p1 → p5) ∨ p2) → ((((p1 → (p2 ∨ p4)) ∧ (p3 ∨ p1)) ∧ (p1 ∧ (p4 → False))) → p2)) ∨ False) ∧ (p1 ∨ True)) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h15 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h16 := h9 h15
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h23 := h5 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h26 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h27 := h20 h26
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45726161732958090597419729635 : (((True → (True ∧ ((((p2 → ((True → ((p2 ∨ p3) ∨ p1)) ∧ True)) ∧ p4) ∨ (False ∧ ((False ∧ p5) ∧ p3))) ∨ (p5 ∨ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248336638005229570134958184747 : ((p2 ∨ p3) ∨ ((((((((p1 → False) → (p5 ∧ p2)) ∨ ((p5 ∧ p4) ∨ p5)) ∧ True) ∧ p3) ∨ p2) ∧ p5) → ((p1 → p2) ∨ (p1 → True)))) := by
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
    let h5 := h4.left
    let h6 := h4.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206279287363289893171431263365 : ((False ∨ (p3 ∨ ((p5 ∨ p1) ∧ True))) ∨ ((p1 ∨ (p5 → (((p1 ∧ False) ∧ p5) → ((((p2 ∧ (True ∨ p1)) ∨ p3) ∧ p3) ∧ p4)))) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115710642099197599979634545045 : (((((p4 → (p3 → False)) ∧ p3) ∨ p3) → (((((False ∧ False) ∧ (p4 → False)) ∧ p2) ∨ p3) ∨ ((p2 ∧ (p3 → p5)) ∧ p1))) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54997368374189498129145958391 : ((((True → p2) ∨ (p5 ∨ (p1 ∧ p4))) ∧ (True ∧ ((p1 ∧ (p1 ∧ p4)) ∨ ((False → p2) ∧ (((p4 ∨ p3) → p3) ∧ (p1 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138282114381133569322361575482 : ((p3 → ((p2 ∧ (((p1 → (p4 ∧ ((((p2 ∨ (p2 → p3)) ∧ p5) ∧ True) ∨ (p4 → p2)))) ∧ p1) ∨ p1)) ∨ True)) ∨ (p5 → (p1 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174258570047137831391906767279 : (((((p4 ∧ (p3 ∨ ((p2 ∧ True) → p2))) ∨ p3) ∨ p2) ∧ (p1 ∧ (p4 ∧ True))) → ((p1 → (((p1 ∧ (p3 → True)) ∧ p5) ∨ False)) ∨ p1)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h3.left
        let h10 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h3.left
        let h15 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246738390314366264723665381923 : ((p5 ∧ p5) ∨ (((((((p2 ∨ (((p1 → p5) ∧ (False ∨ p5)) ∨ p2)) ∨ (p5 ∨ (p4 ∨ p2))) → False) → (True ∧ p2)) → p4) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225405662979135065759702388726 : (((p3 ∨ True) ∧ p1) ∨ (((p4 ∨ (p1 ∧ (False ∧ p5))) ∨ (p4 → p4)) ∨ ((p5 → p1) ∧ ((p4 → p5) → (((p4 ∧ p1) → p2) ∧ False))))) := by
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
theorem thm_5_vars_4504165572357871825972661451 : (p3 → ((((p4 ∨ ((True ∧ p1) ∨ (False ∨ ((((p3 → (p1 ∨ p5)) ∨ p5) ∧ p5) ∧ (p5 → p5))))) → p4) ∨ (p5 → p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338590442899790352475437597837 : (p1 → (((False ∧ p1) → True) → ((((p3 → p4) ∧ (p5 ∧ (((p4 → p2) ∨ p5) ∧ p5))) ∨ (True → ((p3 ∨ p2) ∨ (p4 → True)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191894840084610113911775630892 : ((p5 ∨ ((p2 ∨ (False ∨ ((p2 ∨ False) ∨ False))) ∨ True)) ∨ (p2 → ((p3 ∨ (False ∨ p2)) → ((p1 → (((p1 ∧ p2) → p4) → False)) → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84746254266025743989976789774 : ((((((p2 ∧ (p3 ∨ p5)) ∧ p4) → p5) ∧ (True → (p3 ∧ (p2 ∧ False)))) ∧ ((((p3 ∨ p3) → (False → p5)) → (p4 → p3)) → p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64214559814988084731233324649 : ((False ∨ (p3 ∧ (False ∧ (p1 → ((((p4 ∧ p3) → ((((p4 ∨ True) → p2) ∨ False) ∨ False)) ∨ (p1 → True)) ∧ ((p2 → p4) ∧ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47087150152728862555200159485 : ((((((p3 ∨ p2) ∨ (False ∨ p1)) ∨ (p1 ∨ (p4 → (p2 ∧ (True ∧ (True ∨ (True ∨ (p3 ∧ p2)))))))) → (p1 ∧ p2)) ∨ (False → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342399741387617197689070105079 : (p2 → ((False ∧ ((((p2 ∧ True) → p2) ∨ p3) ∧ ((p5 ∧ ((p3 ∨ p1) ∨ p1)) ∨ p3))) ∨ (p2 → (True ∧ (p3 → ((p4 ∧ p1) → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735415860020245020259058757481 : ((((p4 ∨ p2) ∧ ((p4 ∧ p3) ∨ ((True ∧ False) ∨ (p3 ∨ (((p5 → True) ∨ p2) ∨ (p1 ∨ ((p1 ∧ (False ∧ p1)) → (p3 → p5)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784694770457120218465544975851 : (((p3 ∨ (p4 ∨ (((p5 ∨ ((p2 ∧ p2) → (True ∧ p1))) → (p1 → (p4 → (p2 ∧ (p3 ∧ p5))))) ∨ (((p5 ∨ False) → p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786628718076285021578395544377 : (((p4 ∨ ((((p2 ∨ ((False ∨ p5) ∧ p4)) → False) ∧ p1) → (((True ∨ ((p1 ∨ ((p5 ∨ p5) → (True ∨ p2))) ∨ p1)) → p5) ∨ p1))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54809895540024249401315239801 : (((p3 ∨ ((((p4 ∧ True) ∨ p5) ∨ False) ∨ p4)) → ((((True → p2) ∧ p2) ∨ (((False ∨ p4) ∧ (p2 → p3)) ∨ (p1 → True))) ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47537314012372562362569789392 : (((p4 ∨ (True → (p2 → ((False ∨ (((p1 ∧ p3) ∨ p3) ∧ (((True ∧ (True ∨ (p5 ∧ p3))) ∧ p5) → False))) ∧ p4)))) ∨ (True ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69010399273135406981257239149 : ((p5 → (((p4 → False) → (p1 ∨ ((((p2 ∧ False) → False) ∨ ((True ∨ p5) ∧ (p1 ∨ (True → p2)))) → (p3 ∨ (p4 → p4))))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149389365941925767252974942299 : (((p5 → p2) → (p1 ∧ ((((((p5 ∨ True) → (True ∧ (False ∧ p5))) → (p3 ∨ p4)) ∧ p2) → p4) → p2))) ∨ (False → ((p2 ∨ p1) → p1))) := by
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
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264003417113745295738483674430 : (True ∧ (((p5 ∨ ((((p3 ∧ True) ∧ (p2 ∨ p1)) ∨ False) ∧ p2)) ∨ p2) → (((p5 ∧ (p1 ∨ (p1 ∨ (p4 ∧ False)))) ∧ p5) ∨ (p4 → p4)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
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
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115080383507449633890540750183 : (((p2 ∧ ((p4 → (True ∧ p1)) → ((p3 ∧ p5) ∧ (True ∧ True)))) ∨ ((p1 → p1) ∨ (((p1 ∨ p4) ∨ (p3 ∨ p1)) ∨ p1))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1484772306757790015634618397 : ((((p3 ∨ p4) → (p2 ∧ ((p4 ∨ p2) ∨ (p1 ∧ (p1 ∨ ((p1 ∧ (p5 ∨ ((p3 → p4) ∧ False))) ∨ p5)))))) → p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299115240492064704889724600015 : (False ∨ (((p3 ∨ ((((p5 → True) ∧ (((((p1 ∨ (p1 ∨ True)) ∧ True) ∧ (p3 ∧ p5)) ∧ p3) ∧ (p5 → p4))) → False) ∧ p5)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77534791824105167485225691086 : (((True ∧ ((p4 ∨ p1) ∨ ((p5 ∨ ((((p5 ∧ ((p3 ∨ p3) ∧ False)) ∧ p4) → (True → False)) ∧ p2)) ∨ ((p4 ∧ p5) → p5)))) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((p4 ∨ p1) ∨ ((p5 ∨ ((((p5 ∧ ((p3 ∨ p3) ∧ False)) ∧ p4) → (True → False)) ∧ p2)) ∨ ((p4 ∧ p5) → p5)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261374301730503501127960007684 : ((p5 → p1) → ((((p4 ∧ ((p1 ∨ (((((True ∧ False) ∨ (p2 ∧ p3)) → p3) ∨ (p1 → p5)) ∧ p1)) ∨ p2)) ∨ (False ∨ True)) ∨ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_171968642781502249857628084641 : (((p1 ∧ (p4 ∨ (False ∨ ((p1 → p5) ∧ (p3 ∨ (p3 ∧ False)))))) ∧ (False ∨ p2)) ∨ (True → (True ∨ (((p4 → False) ∧ (p3 → p1)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215337380976090632621348838756 : ((p1 ∧ (p5 ∨ (p4 ∨ p1))) ∨ ((((p1 → p1) → p2) → p2) ∧ ((((p1 → True) ∧ p2) ∨ True) → (((p5 ∧ p1) ∨ p3) ∨ (False → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60902603168495966403374546791 : ((True ∧ (p5 → ((((p4 → p4) ∧ (p3 ∧ p4)) → p1) → ((p3 ∨ ((p3 → (True ∧ False)) ∨ p1)) → ((p1 ∨ (False ∧ p3)) → p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
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
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49332381455893781766959287654 : (((p5 ∨ (((p4 ∧ p4) → (p2 → False)) ∧ (p4 → ((p5 → p4) → (p4 ∧ (((p2 ∧ False) → False) ∧ p5)))))) ∨ (p5 ∧ (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349965878328562394822828012442 : (p4 → (((p4 ∧ ((True ∧ ((p1 ∨ (p1 ∧ p4)) ∧ p3)) ∧ (p3 ∧ ((True ∨ (((p3 ∨ p5) ∨ (p4 ∨ p3)) ∧ p4)) → True)))) ∧ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150976760121502449763929176628 : (((p1 ∨ (p4 ∧ ((((p3 ∧ p4) ∨ (((False → (p3 → p3)) → p2) → p5)) → p3) → (p4 ∧ True)))) ∨ p1) → (p3 ∨ (p2 ∨ (p2 → p2)))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172689277085777553907202709437 : (((p2 ∧ p3) ∨ (((((p4 ∧ (False ∧ p5)) → p5) ∧ (p5 ∨ p1)) → p3) → p2)) ∨ ((((p4 ∧ False) → ((p3 ∨ p3) → p4)) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773993299975986920238954617436 : (((False ∨ ((((True ∨ (((True → p1) ∧ (p4 → p1)) ∨ p4)) ∧ p2) ∨ ((True ∨ p3) → ((p5 ∨ p3) ∧ (p3 ∧ True)))) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178263106676857437872388068651 : ((((p4 ∨ (False ∨ ((False → False) → p1))) ∨ (p3 ∧ False)) ∧ (p5 ∨ False)) ∨ (p3 → (p3 ∨ ((((p5 ∨ p2) ∨ (p3 ∧ p2)) ∧ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156929365037737743428601459018 : (((((True ∧ (p2 ∧ (p5 ∨ ((True ∧ (p2 ∧ (True → p4))) ∧ p1)))) ∧ p4) ∧ (p5 ∨ p3)) ∨ p2) ∨ (((False ∨ False) ∨ True) ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736919998251070174892603679343 : ((((p2 → p5) ∧ (p4 ∨ (((p4 → p1) ∧ (p2 → True)) ∧ ((False ∨ ((((p1 → p2) ∧ (p3 ∧ p1)) ∨ (p5 ∨ False)) ∧ p4)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975519567669610137733104116081 : ((((p4 → p4) → (((((p4 ∧ False) → p4) ∨ p3) ∧ p4) ∧ ((False → (True ∨ False)) ∨ ((p2 ∧ (False → (p5 ∨ True))) ∧ (p3 ∧ False))))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219302844701241725788531597486 : ((p2 ∨ ((False → p2) ∨ p5)) → (((p3 ∨ ((False → p5) ∨ (False → (p3 ∨ (((False → (p4 → p2)) ∧ True) → False))))) → False) ∨ (False → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314285208362826787682608320980 : (p3 ∨ ((p4 → ((((p5 ∨ (((p4 ∨ False) ∧ p4) ∨ p4)) → (((False → p4) ∨ (p4 → True)) → p5)) ∧ p3) ∧ p2)) ∨ (p4 ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_678976287548621540462154904209 : ((((p5 ∧ ((p5 ∧ ((((p5 → (p2 → p4)) → p2) ∨ (True ∨ (p1 ∧ p3))) ∧ p4)) ∧ (p4 ∨ p4))) ∨ ((p2 ∧ True) ∨ (p3 → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337095972037476664854172178714 : (p1 → (((p2 ∨ ((p3 ∧ p2) ∨ (False ∨ (p5 ∨ False)))) ∨ (((((False → p3) → (True ∧ p2)) → p4) → False) → (True ∨ True))) ∨ (False ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197410493361531748480751865468 : (((p1 → (p1 ∧ (p5 ∨ (True → p3)))) → False) ∨ (p1 ∨ ((p3 ∧ (((False → p3) → (p3 ∧ p3)) ∧ ((p1 ∨ p1) ∨ True))) → (p5 ∨ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44052236960506963855542148686 : ((((p2 → (p4 ∨ ((((((p5 ∨ p2) ∧ False) → ((p1 ∨ p4) ∧ p4)) → p2) ∨ (p2 ∧ (p5 → p3))) ∨ p5))) → (p5 ∨ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172046994922971816180748590124 : (((p4 → ((p5 ∨ (p5 ∨ (p4 ∧ True))) → (False ∨ (False ∨ True)))) ∨ (False ∨ p2)) ∨ ((True ∧ (p5 ∧ (p1 ∧ p3))) → (p4 → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180957039635541507055479513423 : (((p5 ∨ p1) ∧ (p5 → (((p4 ∨ (False ∧ True)) ∧ (p4 → p5)) ∨ p5))) → (((p2 → (p1 → p1)) → p5) ∨ (False → ((p3 ∨ p2) → True)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746061287500654288006341666861 : ((((p1 ∨ False) → (((((p1 → (p1 → (p4 → p1))) ∨ (((p2 → p5) ∧ ((p3 ∨ p5) → p1)) ∨ p5)) ∧ p3) → (p2 ∧ False)) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792099833951634738413584358609 : (((True → (((((p3 ∧ p3) ∨ ((False ∨ True) ∧ (p1 ∧ p3))) ∨ (((p4 ∧ False) ∧ p3) → False)) ∨ (p1 → p2)) ∨ (p5 ∧ (p4 ∧ False)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55448730494826057935991714653 : (((((p3 ∨ True) → (p1 ∧ p1)) → p2) → ((((((p2 ∧ ((p3 ∨ p5) ∧ False)) ∧ p2) → p3) ∧ ((p4 → p4) → p2)) → p3) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65539087131602740053316555349 : ((p3 ∨ (p5 ∨ ((((((False ∨ p1) → False) ∨ (p2 ∨ p4)) ∧ True) ∧ p4) ∨ (((p2 ∨ (p5 ∧ (p5 ∨ p2))) ∧ (p5 ∧ p4)) → p4)))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
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
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204640309262784254370695521801 : (((p1 ∧ ((p4 → True) → False)) ∨ p4) ∨ ((p3 ∨ ((((True → (True ∧ True)) ∧ (True → (True ∨ (True → (p4 ∧ p4))))) → p2) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_228639813580961820354201993298 : ((p2 ∨ (False ∧ p2)) ∨ (((p2 ∨ p3) ∨ (p5 ∨ False)) → ((p5 ∨ (False → ((((p2 ∨ (p2 ∧ True)) ∨ p1) → (p4 → p3)) → p2))) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763699251454084037317896234774 : (((p3 ∧ (False ∨ ((((False → p2) ∨ (((p3 ∧ p3) ∨ (((True ∧ p2) ∨ (p3 ∧ p4)) ∨ p3)) → p5)) ∨ ((p1 ∧ p3) → True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48619977424619814816960911643 : ((((True → (((((((p1 → True) ∧ (True ∧ p3)) → p4) ∧ p2) ∨ (p1 ∨ p1)) → p5) ∧ False)) → (False ∨ p4)) ∧ ((False → p5) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62467447970687168853374908817 : ((p3 ∧ ((p2 ∧ p5) ∨ (((p5 → ((p2 ∨ (False ∧ (p3 ∨ p3))) ∧ (p2 → (p2 → p2)))) ∨ (p1 → (p1 ∧ p1))) ∨ (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139540484280373219340168537950 : ((((((p3 → ((False ∧ False) ∧ p5)) ∨ (False → ((p2 → (p5 → (True ∧ p4))) → p4))) ∨ p4) ∨ (p3 ∨ True)) → False) → ((p3 ∨ p2) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 → ((False ∧ False) ∧ p5)) ∨ (False → ((p2 → (p5 → (True ∧ p4))) → p4))) ∨ p4) ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 → ((False ∧ False) ∧ p5)) ∨ (False → ((p2 → (p5 → (True ∧ p4))) → p4))) ∨ p4) ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151380826503841831573918603119 : (((((((p4 ∨ (p4 → (False → True))) ∨ ((False → False) ∨ p1)) → p1) ∧ True) ∧ (p2 → p3)) ∧ (p5 ∨ True)) → (False ∨ ((False → p5) → p1))) := by
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
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 ∨ (p4 → (False → True))) ∨ ((False → False) ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h10
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : ((p4 ∨ (p4 → (False → True))) ∨ ((False → False) ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h19 := h6 h16
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736334381900658582099455535964 : ((((False → p5) ∧ (((((p2 → ((((p4 ∧ (p5 → p1)) ∨ (True → ((p5 → True) ∧ True))) → p4) ∨ p2)) ∧ p2) ∨ False) ∨ False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116046937268118807338421872682 : (((False → (p3 ∧ (p4 → p2))) → (((p2 → (False ∨ ((((p2 ∧ p3) ∨ p3) ∨ p4) ∨ (False → False)))) ∨ True) ∨ (p2 → True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744305733214409282081966027017 : ((((p1 ∧ p4) → (((p5 ∨ p3) ∧ ((True ∧ (p4 ∨ p5)) ∨ p2)) ∨ (False ∧ (((p3 ∧ (((True ∨ p5) → True) → False)) → p1) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351519050557676759648288943092 : (p4 → (((((p2 ∧ ((p4 ∨ p5) → ((p3 ∨ p1) ∧ ((p5 ∨ p5) ∧ False)))) ∨ p4) ∨ p2) ∨ p5) ∨ ((p2 ∧ (p1 ∧ (False ∧ p3))) → p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116055385078669062031158575370 : (((p5 → ((p2 ∧ p4) → p4)) → (((False → False) → (p4 → (p1 ∨ p2))) → (((p5 → p1) ∨ ((True ∧ p5) ∧ p3)) ∨ True))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314479568927074525876980508298 : (p3 ∨ (((False → False) → ((p5 ∧ ((((p1 → (False ∨ p2)) → (True → p5)) → p1) ∨ p5)) ∧ (p1 ∨ False))) → ((p4 → p5) ∧ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620671084394612958453976394501 : (((((p1 ∧ True) → ((((((((p1 → (((p4 ∧ False) → p5) ∨ p4)) ∧ p2) ∧ p5) ∨ p5) ∧ (False ∨ p5)) → p4) ∨ p2) ∨ False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_49101911924376853244174232692 : ((((((p3 ∧ p3) ∧ (((p1 → p2) → p1) ∨ p4)) → ((p2 ∨ (p3 ∨ p5)) → False)) → ((p1 ∨ True) → p1)) ∨ (p3 → (p3 → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165028499625203676400913194486 : (((((False ∧ True) → p2) ∨ (p5 ∨ (((p4 ∨ p5) → p2) ∨ ((p2 ∧ p4) ∧ False)))) → p3) ∨ ((((False ∨ p3) → (p4 → p4)) ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43094900610622093792912375155 : (((((p5 ∧ (((True ∨ ((((p1 → p2) ∧ p2) ∨ ((False ∨ p3) ∧ (True ∨ p3))) ∨ p3)) ∧ p4) ∧ p2)) → (p5 ∨ False)) ∧ True) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214224547994759405349373180490 : ((((p5 → p5) → p1) → p3) ∨ ((((p4 → p2) ∨ (p5 ∨ False)) ∧ (((p2 ∧ p3) ∨ ((True → False) → False)) → p2)) → ((p1 → p2) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∧ p3) ∨ ((True → False) → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : ((p2 ∧ p3) ∨ ((True → False) → False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h13
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : ((p2 ∧ p3) ∨ ((True → False) → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h26 := h20 h22
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h29 : ((p2 ∧ p3) ∨ ((True → False) → False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- False on the left can always be used.
        apply False.elim h32
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h33 := h20 h29
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356072451725329625606354422368 : (p5 → ((((p1 → p5) ∨ (p5 ∧ (p3 ∨ ((p5 → ((True ∧ p5) → p5)) ∧ False)))) ∨ (p2 ∨ (p1 ∨ p1))) → (p4 ∨ (p5 ∨ (p3 ∧ False))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219550478170544933411098160541 : ((True → ((p3 ∧ p1) ∧ p4)) → (((p2 ∨ False) → ((p4 → (False ∨ p1)) ∨ p1)) ∧ (((True ∨ p1) → ((p4 → (p5 → True)) ∧ p4)) ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693071531073851507455713604503 : ((((p1 ∧ ((False → (p3 ∧ p5)) ∧ (p4 ∨ ((True ∧ (p5 ∧ p4)) → False)))) ∧ (((p2 → p4) ∨ (p5 → (p3 ∧ p2))) → (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179765935036135206948393939794 : ((((((p3 → p1) ∧ True) ∧ (p1 ∧ p5)) → (p5 ∨ (True ∧ p4))) ∧ p5) → (((p5 ∨ False) → p2) → ((False ∨ (p1 ∨ (True ∧ False))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303905790654992252859813120965 : (p1 ∨ (((((((True ∧ False) ∧ p3) → (False ∧ p2)) ∨ p4) ∧ (p1 → (True → p3))) → ((((p4 → p3) ∨ p5) ∧ p2) ∧ (p1 → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64562550432533974784683245596 : ((p1 ∨ (((p4 ∧ p4) ∨ True) ∧ (True ∧ (((True ∨ p4) ∧ (True ∨ False)) → (p4 ∨ ((p2 ∨ (True → (p4 ∧ (p4 → True)))) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265724784970986327124811677524 : (True ∧ (p3 ∨ (((p5 ∧ p5) ∧ p1) ∨ (((((p2 ∧ p1) ∨ True) → p2) ∨ (True ∨ p3)) ∨ ((p2 ∨ ((p1 ∨ (p3 → p3)) → p4)) ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_54237502007580716776534896782 : ((((p1 → (((p2 ∨ p5) → p3) ∨ True)) → p2) ∧ ((True ∨ ((p3 → ((True ∧ ((p1 ∧ p3) ∧ (p4 → p3))) ∧ p3)) ∧ True)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302863694434927740866172735356 : (False ∨ (True → ((False ∧ (((((False ∧ p3) ∧ (((p3 ∨ True) ∨ p3) ∧ (p1 ∧ (p5 ∨ p2)))) → ((p4 ∨ True) ∧ p3)) → p1) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391511421825474339184053410789 : (((((((False → p1) → p3) → False) ∧ (((p2 → (p3 ∨ p4)) → p3) ∨ ((p3 ∨ ((((p3 → True) ∨ p5) ∨ p2) → p5)) ∧ p3))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_263561770931262890673108230067 : (True ∧ ((((True → False) ∧ (((p4 → p2) ∨ ((((False ∨ p3) → p2) → p5) ∨ False)) ∧ p4)) ∨ (True ∧ p3)) ∨ ((p5 → p4) ∨ (False → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149028639541450556363716022118 : ((((p2 → p5) → p1) ∨ ((p4 ∨ (p3 ∨ False)) ∨ ((p2 → ((False ∧ p5) ∨ ((False ∨ p1) → p2))) ∨ p1))) ∨ (p4 ∧ ((True → p5) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162936210379483071156110047738 : (((((False ∧ p4) → (False → p5)) ∨ (p2 ∨ ((p4 → (True → p5)) → p5))) → (p3 ∨ True)) ∧ ((False ∨ (p3 ∧ False)) ∨ ((False ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



