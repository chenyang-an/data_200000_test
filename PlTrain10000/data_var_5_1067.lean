variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119064058773212313970661658367 : ((p1 → ((p1 ∨ (((True ∨ p4) ∨ p2) → (p5 → (True ∨ (((p5 → (p3 ∧ (True ∧ (p4 ∨ p5)))) → p2) ∨ False))))) → p4)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308524998737503261042515688012 : (p2 ∨ ((((p5 ∨ (((p2 → p4) → p4) ∧ ((p5 ∧ p3) ∧ (p3 ∨ p3)))) ∨ False) ∨ ((p3 → (((p1 → p1) ∧ False) ∨ p1)) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129327302737796841172234902393 : ((((p3 ∨ p3) ∨ (((((p2 ∧ ((True ∨ p2) ∧ (p2 ∧ p5))) ∨ False) ∨ (True → (p4 ∨ p5))) ∨ False) ∨ True)) ∨ p1) ∧ ((False ∨ True) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308429854523023185275718883040 : (p2 ∨ ((((p4 ∨ (True → p3)) ∧ ((p3 ∨ (p4 → True)) ∧ (False ∨ ((False → (p4 ∧ p1)) ∧ (p3 → (p2 → (p2 ∧ p1))))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146348860822017186549348459124 : ((p1 ∨ ((p1 → (p1 → (((p4 ∧ (True ∧ ((p3 ∨ p5) ∧ p3))) ∨ p1) ∧ (True ∨ (p3 ∧ p1))))) ∨ p4)) ∧ ((False → True) ∨ (p5 ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134587053004668481460717846512 : (((((p5 ∨ p3) ∧ (((p2 ∨ p5) ∧ ((p4 ∨ p4) → (((True ∧ p4) ∧ False) → True))) → p1)) ∨ (p3 → p3)) → p5) ∨ (p3 ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115754087075085432492694936889 : (((p2 ∧ (p4 ∨ ((p3 → False) → False))) → ((p1 ∨ (p4 ∧ (p3 ∨ p3))) → ((p1 ∧ p2) ∨ ((False ∨ p2) ∧ (True → True))))) ∨ (p5 → p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311805391172133732394991151465 : (p2 ∨ (p1 ∨ ((((p3 → p1) ∨ p5) ∧ (((False ∧ (p3 ∨ p5)) ∨ ((p2 → p5) ∨ (((p5 ∧ p1) ∧ p3) ∧ (p1 → True)))) ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49653900717886916359450653846 : (((((False → True) ∨ p5) ∧ ((((p1 ∧ True) ∧ (True ∧ p1)) ∧ ((True ∨ p1) → False)) ∨ (False → (p4 ∧ False)))) → ((p2 ∨ p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317843535465093275877285024538 : (p4 ∨ ((((False ∨ p3) → p1) → (True → ((((p1 ∨ p2) ∧ ((p4 ∧ (True ∨ p5)) ∧ (p4 → True))) → (p1 ∨ (p4 ∧ False))) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302621970358001873998039462254 : (False ∨ (p2 ∨ ((p1 → (p2 → (True ∧ ((((True ∨ (p3 → True)) → ((p4 → False) → (p2 ∧ p5))) → (p2 ∨ False)) → (p5 ∧ p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180604474170067327334908674114 : ((((((True ∧ p1) ∧ p5) ∨ p3) → True) ∧ ((p4 → p3) ∨ (p3 → False))) → (p3 → (((p2 → (p2 → True)) → (p2 ∧ p2)) ∨ (False → p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156628528279878531175417069701 : (((((((p5 → p5) ∧ ((p3 ∧ True) → p5)) ∨ p2) → (p4 ∨ ((p4 ∧ p3) → p5))) ∨ p2) ∧ p4) ∨ (p4 → (p4 ∨ (p3 ∧ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174369605134994446749772982090 : (((p5 → (((p1 ∧ p3) → (p2 ∨ True)) ∧ (p2 ∧ False))) → ((p5 → p2) ∧ p1)) → (p4 ∨ (((p4 → False) ∨ (p1 → (p4 → p1))) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139934993363499206654135094448 : (((((False ∨ p1) ∨ p3) ∧ (((((True ∨ p3) ∨ p2) ∨ (p5 ∨ p3)) ∨ ((p4 → p3) ∧ True)) → False)) ∧ (p1 → p2)) → (p3 ∧ (p5 → False))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : ((((True ∨ p3) ∨ p2) ∨ (p5 ∨ p3)) ∨ ((p4 → p3) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h20 : ((((True ∨ p3) ∨ p2) ∨ (p5 ∨ p3)) ∨ ((p4 → p3) ∧ True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h21 := h16 h20
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h23 : ((((True ∨ p3) ∨ p2) ∨ (p5 ∨ p3)) ∨ ((p4 → p3) ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h24 := h16 h23
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54690969688536476432546229736 : ((((p5 ∨ (p4 → ((p2 ∧ False) → False))) → p3) → (((p4 ∨ p4) ∧ (p1 ∧ p1)) ∨ ((p1 ∧ ((True ∨ True) ∨ False)) ∨ (False → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618824134595956294429051538253 : (((((p5 ∧ (p4 ∨ p5)) ∧ ((p5 ∧ (p5 ∨ ((True ∨ (p5 ∧ ((p3 → p1) → (False ∧ (p5 ∧ p2))))) → (p3 ∧ p2)))) ∨ p2)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782318159124121136900997159014 : (((p3 ∨ ((p2 → ((p3 ∧ (p5 → (((False ∨ (p4 ∧ False)) ∨ ((p3 → p2) ∨ p5)) → (((p3 ∨ p1) → False) ∨ True)))) ∨ p2)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314009259152792042765905096688 : (p3 ∨ ((p2 ∧ (((p3 → p4) ∧ False) ∨ ((p5 ∨ False) → ((p1 → (((p4 ∧ (p5 ∨ p3)) → p1) ∨ (p3 → False))) → p2)))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241380602156173068881055257273 : ((False → False) ∧ (p3 ∨ (p5 ∨ (((p2 ∧ (p2 → p5)) → ((p4 ∧ p5) ∨ ((((True ∧ p3) ∧ p3) → (False → p5)) ∧ p5))) ∨ (p1 → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57324098106674183080397822182 : (((False ∧ (p5 ∨ p4)) ∨ ((((p4 ∨ p2) ∨ ((False ∨ p3) ∧ (p4 → (p5 ∨ (p4 → (p4 → False)))))) ∨ p5) ∨ (p2 ∨ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113278853027556150892359276274 : (((((((True → (p3 ∨ p3)) ∨ p2) → ((p2 ∧ True) ∧ False)) ∨ True) ∧ ((((False ∨ p3) → p3) ∨ p4) ∨ p4)) ∧ (p3 → p3)) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350641533278673006824057528758 : (p4 → (((True → p5) ∧ ((((p4 ∧ ((False ∨ False) ∧ p2)) → p1) ∧ (p3 → False)) ∧ (False ∨ ((p4 ∧ p4) → ((p3 ∨ p4) ∧ False))))) → False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p4 ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158544456528571075945565041627 : (((p3 → p1) → (p4 → (((((p3 ∨ p3) → (True ∧ False)) → p4) ∨ (True → True)) ∧ (p5 ∧ False)))) ∨ (p3 ∨ (p5 → ((p2 → False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114440973824675561586789257670 : (((True → ((p4 ∨ ((False → p4) → (p4 → p1))) → (True → (False ∨ (p1 → (p5 ∧ p1)))))) ∨ ((p1 → p4) ∨ (p3 ∧ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427656744278851488647406483309 : (((((((False → p2) ∧ (p5 → ((p4 ∨ (p2 ∨ (p4 ∨ ((((p2 → p1) ∨ p1) → p3) → p4)))) → p4))) ∨ False) ∨ True) ∨ (p2 ∧ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230540657050724375113514209296 : (((False → p2) ∧ p2) → (p3 ∨ ((p4 ∧ p3) ∨ (((p2 ∧ (p3 → p2)) ∨ (((p5 ∧ ((p3 ∧ p3) → False)) ∨ p5) ∨ (p4 → p3))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690188561901585260396658237693 : ((((p3 ∨ ((False ∧ (p5 → p4)) ∨ ((((p2 ∨ p1) ∧ p4) ∨ p5) → (p3 ∨ p2)))) ∨ (p3 ∨ (p4 → (p4 ∨ ((p1 ∨ p5) ∨ False))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172176284454268498360047293735 : ((((p1 → True) → (p3 → ((p2 → True) ∧ (p2 ∧ p4)))) ∨ (p5 ∨ (True ∨ p4))) ∨ ((p3 → (p3 ∧ (p1 ∧ p2))) ∨ ((True ∧ True) ∧ False))) := by
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
theorem thm_5_vars_258761450857098064333843219401 : ((True → False) → ((p2 ∨ ((p1 ∨ True) ∧ (((False ∨ ((True → (p3 → p3)) ∧ ((False ∧ p2) ∧ p3))) ∨ p4) ∧ (p2 → (p2 → p5))))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158567913295813074433806006943 : ((True ∧ ((((True ∨ True) ∧ ((p5 ∨ (p4 → (p3 → p3))) → False)) → p5) ∧ ((p1 → p5) → p2))) ∨ ((False ∧ (p4 → (False ∨ p4))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316507993919635631198029066920 : (p3 ∨ (p2 ∨ ((((((p3 → p2) ∧ p5) ∧ (False ∨ p1)) ∧ (False ∧ (p2 → p1))) → p4) ∧ (((True ∨ (p4 → p3)) → (p2 ∨ p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- False on the left can always be used.
    apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308627851241535920481142315935 : (p2 ∨ (((False ∨ p4) → (p5 ∨ (p5 → ((((p2 → p1) → ((p4 ∨ (False ∧ p2)) ∧ ((p3 ∧ True) ∨ p2))) ∧ (False ∧ True)) ∨ True)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134378960226645630996769573643 : (((p3 ∨ (p4 ∨ ((False ∧ ((((p2 ∨ p5) → (p4 → (False → p2))) ∧ p3) ∨ p3)) ∧ ((p2 → p5) ∨ p5)))) ∨ True) ∨ (p1 → (False ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590476102765726379647808099660 : ((((((p4 → p1) ∨ (((p4 → (((False ∨ False) ∧ False) ∨ (True ∨ p3))) ∨ ((p1 → p5) ∧ (p5 ∧ (True ∨ False)))) ∨ p4)) → p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148822376444295716421181900861 : (((False ∨ ((p5 ∧ p4) ∨ (p5 ∨ p3))) → (True → (p3 → ((p1 ∧ ((p2 ∨ True) ∧ False)) ∨ (True → True))))) ∨ (((p1 → False) → p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628579721247876612062816517319 : (((((p1 ∨ (((p5 ∧ ((p1 ∧ p5) ∨ True)) ∨ p4) → (((False → p4) ∧ (p2 → (p4 ∧ False))) ∧ (True ∨ (False ∧ p1))))) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798390896036603859689820136723 : (((p1 → (((((p3 ∨ (p1 ∧ True)) ∧ False) → p2) → (p4 ∧ (p1 → p5))) ∨ ((((p4 → p1) ∨ True) ∧ p3) ∨ ((False ∧ p4) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305627458274564845890582547215 : (p1 ∨ ((p3 ∧ ((p5 ∨ p2) → (p4 → (False ∨ (False ∨ (p4 ∨ p3)))))) → (((p5 → p4) ∨ (p3 ∨ (False → False))) ∨ ((p3 → p1) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356138835610634817694608312686 : (p5 → ((((((p4 ∧ ((True ∧ True) → p3)) ∧ (((p3 ∧ p2) ∧ p4) ∨ p3)) ∨ False) → False) ∧ p2) ∨ (((p4 ∨ p1) ∧ (False ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347835040331171946081742270929 : (p3 → (((p4 → p2) ∨ True) → (((p5 ∧ (p4 ∧ (True → (((p2 ∨ (p5 ∧ p4)) → (p1 ∨ p1)) ∧ p3)))) → p1) ∧ (p1 ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p2 ∨ (p5 ∧ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h18 := h7 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : (p2 ∨ (p5 ∧ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610195057603942913260424510587 : (((((((((p4 → ((p1 ∧ p2) → (p4 → True))) → p5) ∨ (p3 → (False ∧ (((p1 ∨ False) ∨ False) ∧ p1)))) → p2) ∨ p4) → p2) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149433441999712966530556778241 : ((True ∧ (p5 ∨ (((p2 ∧ p2) → p3) ∧ ((p5 ∨ (p3 → False)) ∨ ((p2 ∧ (True ∧ (p1 ∨ p3))) ∧ True))))) ∨ (p3 → (p4 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_114006924476856277711415500314 : (((((((True ∧ (p2 → (p3 ∧ p1))) → p2) → p2) → (p3 ∧ (((p1 ∨ p1) → False) ∧ p3))) ∧ p4) ∨ ((p1 ∧ p3) ∧ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150966439721849281807657193434 : (((True ∨ ((((((p5 → False) → p4) ∨ p5) ∧ p2) ∧ p5) ∧ ((((p1 → p3) ∨ p1) ∨ False) ∨ p5))) ∨ True) → ((p5 → p4) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h17 =>
              -- One of the premise coincides with the conclusion.
              exact h3
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h24 =>
              -- One of the premise coincides with the conclusion.
              exact h3
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h3
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164908982855618470569363098894 : (((((True → False) ∧ ((((p5 ∨ True) ∧ p3) ∧ p4) ∨ ((p1 → p5) ∧ True))) ∧ True) → False) ∨ (p4 → ((p1 → p1) → ((p1 ∨ p1) ∧ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208535636513195660797716386561 : (((False ∨ p1) → ((True ∨ p1) ∧ False)) → ((p3 ∨ (True ∧ ((p2 ∨ (((p1 → p5) ∧ False) ∨ (p2 ∧ p4))) ∧ ((p5 → False) ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53872327347430067812483383347 : ((((True ∧ p2) ∨ (p3 → (p4 → (p3 ∧ (p4 → p5))))) ∨ (((p1 → True) → (p2 ∧ False)) ∨ (((p3 → p1) ∨ True) ∨ (p5 ∧ False)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_192710179020602921692799625937 : ((((False ∨ (False ∨ False)) ∧ (p2 ∧ (p4 ∧ p4))) → False) → (p1 ∨ (p5 ∨ (True → ((((p2 → False) → p4) ∨ p5) ∨ (False → (p5 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116562853067580558150778988214 : (((p2 ∨ p1) ∧ ((p1 ∧ ((((((p3 → (p3 → True)) → p3) ∨ p2) ∨ p5) → (p1 → p3)) → (True ∧ p2))) ∨ (p4 → p4))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327139949530913999546294292848 : (True → ((p1 ∧ (((((p1 ∨ p5) ∨ p4) ∨ ((p4 → ((p4 ∧ (p3 ∨ p3)) ∨ p4)) → p2)) ∨ p2) ∧ ((p3 ∧ (p2 ∧ p4)) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199481164495896646843416464207 : (((p3 ∨ (True ∧ (p4 ∨ (p1 ∨ p4)))) ∨ p1) → ((False ∨ ((p3 ∨ ((p2 → (p3 ∨ False)) → (False ∧ p5))) ∨ True)) ∧ (True ∨ (p3 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341718665843949878241816967006 : (p2 → (((((p3 ∧ False) → p4) ∧ (p5 → (p4 ∧ True))) ∨ ((False → (p2 → ((False → (p2 ∧ (True ∨ p5))) ∧ p2))) → False)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199316995699170001046820531221 : ((((p1 ∨ (p1 → (p1 → p3))) ∨ p4) ∨ p4) → ((p3 ∨ ((((False → p2) → p4) ∨ (True ∨ p3)) → (False ∧ False))) → ((p4 → p1) → p3))) := by
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
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h8 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h15 : (((False → p2) → p4) ∨ (True ∨ p3)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h16 := h11 h15
          -- We need to get the left conjuct of h16 based on <expert-advice>.
          let h17 := h16.left
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h19 : (((False → p2) → p4) ∨ (True ∨ p3)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h20 := h11 h19
          -- We need to get the left conjuct of h20 based on <expert-advice>.
          let h21 := h20.left
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h23 : (((False → p2) → p4) ∨ (True ∨ p3)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h24 := h11 h23
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h27 : (((False → p2) → p4) ∨ (True ∨ p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h28 := h11 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131596821901369195095830638817 : ((((False ∨ p2) ∨ p2) ∨ ((p3 → True) ∧ ((True → True) ∧ (p1 → ((p4 → (p5 ∨ ((p5 ∨ p1) → p2))) ∨ True))))) ∧ (True → (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186793103220372220353131763507 : ((((True ∧ (False ∧ False)) → p2) ∧ (p2 → ((False ∨ p1) ∨ p2))) → ((((True ∧ p3) → (False ∨ p5)) ∧ (p3 → p5)) → ((p2 ∨ False) → p2))) := by
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
    let h7 := h1.left
    let h8 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134138434581636171562238227851 : ((((p4 ∧ (p1 ∧ ((True → p1) ∧ ((((p1 ∨ (p4 → p3)) ∧ (False → p4)) ∨ p2) ∨ p2)))) → (p3 ∨ p2)) ∨ p3) ∨ ((p3 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157291779550435157141270444413 : ((((p1 → p5) ∨ ((p1 ∨ (p5 ∨ (p2 ∨ False))) → ((True ∨ (p4 → (p4 ∨ p4))) → p2))) → p5) ∨ ((p3 ∨ True) ∨ ((p2 ∨ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94876670197179666838931555725 : ((p3 ∧ (p3 ∧ (p3 → ((p1 → ((((((True → (p5 ∧ p3)) ∨ p2) ∨ False) ∨ (False ∨ True)) ∨ p4) ∧ ((p5 ∨ False) → p3))) ∧ False)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593845502909788772755752616865 : ((((((p4 → ((((p2 ∧ ((False → p2) ∧ (p5 ∨ True))) ∨ p3) ∧ (p1 ∨ p4)) ∨ p3)) ∧ p1) ∨ ((p1 ∨ True) → (p4 ∧ p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148130431718434222881406644334 : ((((p2 ∧ p3) ∨ ((p2 ∨ p5) ∨ ((p1 ∨ (((p5 → p3) → (True ∨ p3)) ∧ p2)) → p5))) → (p4 → p1)) ∨ ((False → p5) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227391581961324001526080120076 : (((p4 → p2) → p2) ∨ ((p2 → p2) → (p2 ∨ (((False ∧ p3) ∧ (False ∨ (False ∨ (True ∨ ((p4 → True) ∨ p3))))) ∨ ((False → p5) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116290604399173132587451891200 : (((p4 ∨ (p2 ∧ False)) ∨ (p4 ∧ ((p2 ∧ (p3 ∧ p3)) → (((p3 ∨ (p5 → True)) → (False ∧ p5)) ∧ ((True ∨ False) ∧ False))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184245701437883075017239962048 : (((((p2 ∧ p2) ∨ (p2 → (True ∧ (p5 ∨ p2)))) → p3) → p5) ∨ ((p3 ∧ (p1 ∧ (p2 ∧ p2))) → (p5 ∨ (p2 ∨ (p5 ∧ (p5 → p4)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174904317067719535991411194476 : (((p5 ∧ p5) → (((((p1 → (p5 ∨ p5)) ∨ p1) ∧ (p3 ∨ p5)) ∧ p4) ∧ True)) → ((p1 ∧ (p1 → p2)) ∨ ((True ∧ (p4 → p4)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742645120755263781840065314299 : ((((p2 → p4) ∨ ((((p2 ∨ ((p5 ∧ True) → (p3 ∧ (((p2 → p2) ∨ p5) → (p2 ∧ p1))))) ∧ (p3 ∨ p1)) ∨ False) → (p2 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631855989220568143428960630578 : (((((((p2 → (p4 → (p5 ∨ p3))) ∧ p4) ∨ ((p4 ∨ p5) → (True ∨ (p5 ∧ (((p3 ∨ p3) ∨ True) ∧ (False ∨ False)))))) → True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257636071479857206880638559972 : ((p3 ∨ p2) → (((False ∨ p5) → ((True → p1) → p1)) ∧ ((p3 → p2) → ((p4 → ((p1 ∧ p5) ∨ (p5 ∨ p2))) ∧ (p2 → (p2 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h13
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300921716959767628072771061548 : (False ∨ ((p1 → ((((p5 ∧ p4) ∨ p5) ∧ p5) ∨ ((False ∧ (True ∧ p1)) ∨ False))) → (((p5 ∧ p5) ∧ (p2 → (True ∧ (True → False)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3459579476859326462004974898 : (True ∧ (False ∨ (((p5 ∨ ((p1 → p4) → ((p2 ∨ (p2 ∧ (True → ((False ∨ False) → p4)))) ∨ (True ∧ p1)))) ∨ (True → True)) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111284026631088589118783094448 : ((((True → p1) → ((((((((p5 → p3) ∨ (True ∨ p2)) ∨ p3) ∨ (p5 ∨ p1)) → (p4 ∨ p2)) ∧ p2) ∧ p1) ∧ False)) ∧ p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258789707974962583152037807813 : ((True → False) → ((((p4 → True) ∧ (p5 ∨ p4)) ∨ True) ∧ ((((True → (((False ∨ p3) ∧ p2) ∧ p5)) → p5) ∨ p4) ∧ (p5 → (False ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705436316288816572034153313469 : (((((p3 ∨ (True → (True ∧ (p5 → p1)))) ∨ p5) ∧ (False ∨ (p3 ∧ (False ∨ ((((p1 → (p5 → (False ∧ p3))) → p1) ∧ p1) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_976103662661190669595426665599 : (((True ∧ ((True → ((p5 ∨ ((((p1 → p4) ∧ p1) ∧ p2) → ((((p4 → p5) ∧ False) → True) ∧ (p1 → p4)))) ∧ (p5 ∧ p3))) ∧ p2)) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876255287235934419774123594732 : (((((((p3 → p3) → (((p5 ∧ p3) ∨ (False ∧ ((False → (p2 ∨ p1)) → p3))) ∧ (True → p3))) ∨ p2) → (True ∧ p5)) ∧ (False ∨ p2)) → p5) ∧ True) := by
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
    have h6 : (((p3 → p3) → (((p5 ∧ p3) ∨ (False ∧ ((False → (p2 ∨ p1)) → p3))) ∧ (True → p3))) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718217529175040811330824502246 : (((((p4 ∨ (p5 → p1)) ∨ p3) ∨ ((p1 → ((p3 ∨ p5) ∧ (p2 ∨ (p1 ∧ ((p1 ∨ p3) ∧ p1))))) → (((p5 ∧ True) ∧ p2) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217879763572418267979878536287 : (((p1 → (p5 ∨ True)) → True) → (p4 → ((((False ∧ True) ∧ True) ∨ (p4 ∨ False)) ∧ (p4 → (p1 ∨ ((p3 → ((p4 ∧ False) ∧ p2)) ∨ p4)))))) := by
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
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65675472354169495662363154209 : ((p4 ∨ (((((((p1 ∧ p1) ∧ p3) ∨ (p5 ∨ p5)) → (True ∨ (False ∧ ((p4 ∨ p5) ∨ True)))) → p4) → (p3 ∧ (p1 → p4))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262641098999279181708839545000 : (True ∧ (((((((((p2 ∨ (((p4 → p3) → p1) → p2)) ∨ p1) ∧ (False ∨ True)) → p2) ∨ (p5 ∨ p3)) ∨ p3) ∨ p2) ∧ (True → p4)) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h8 := h3 h7
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h11 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h12 := h3 h11
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h15 := h3 h14
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h20
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114660610547011046137646523187 : (((((True ∨ False) ∨ (p3 ∧ p4)) → ((True ∧ (p5 → ((p3 → p2) → False))) ∧ p5)) ∨ (((p1 ∨ p2) ∨ (True ∨ p2)) ∨ True)) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136903797186636162953895908187 : (((p5 ∨ p3) ∨ (((((p1 ∨ (p2 ∨ False)) ∨ p3) → ((p1 → ((p3 → p5) ∧ p2)) → (p1 ∨ p4))) → p1) ∧ p3)) ∨ (p4 → (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666973524289157453724523126008 : (((((((False ∨ p5) → True) ∧ p3) ∨ (((True ∨ p1) → (p2 ∧ True)) → ((p1 ∨ (p3 → (p1 → False))) ∧ True))) ∧ ((p4 ∨ p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136095370936332494963693079222 : ((((True ∧ ((p1 → p3) ∧ (p5 ∨ p4))) ∨ p5) ∨ (((p4 → ((((p1 → p3) ∨ True) ∨ p2) → False)) ∨ p3) ∧ p1)) ∨ (True ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187614690440851963361248282785 : ((p4 ∨ (False ∧ (p2 → ((p4 ∧ p5) → (p3 ∨ (True ∨ p2)))))) → ((p1 ∨ ((p4 ∨ p3) ∧ (p4 ∨ (p5 ∧ False)))) → (False ∨ (p3 ∨ True)))) := by
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
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- False on the left can always be used.
          apply False.elim h24
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24143598326871887230637111940 : (((p2 ∧ (p1 → (False ∨ p5))) → (((p2 ∧ False) ∧ p3) ∨ (p4 ∨ (p1 → ((((False ∨ False) ∨ p5) ∧ (p2 → (p5 ∧ p1))) ∧ p2))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321139598782075181263408353114 : (p4 ∨ (p2 ∨ ((True → ((False ∧ True) ∧ p3)) → (p2 → ((p5 ∧ ((p2 ∧ ((p5 ∨ p2) ∧ p5)) ∨ (p2 → (p1 → p2)))) ∨ (True → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219822954521614899781352136432 : ((p3 → ((p4 → p3) ∧ True)) → (((((((False ∧ True) ∨ True) ∨ (True ∧ True)) ∧ True) → p5) → ((p1 → ((p2 → False) → p4)) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55133846541637602077274716151 : ((((p5 ∨ (p2 ∧ (p3 ∨ p4))) ∧ p3) ∨ (((True → (p1 ∨ True)) ∧ (p3 ∨ False)) ∧ (p4 → ((p4 → ((True → True) ∨ p5)) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150002804305412629975684128304 : ((p5 ∨ ((p5 ∨ ((p5 ∨ (p5 → p2)) → (p1 ∨ ((((p1 ∨ (False ∨ p3)) → p4) ∧ p1) ∧ False)))) ∧ False)) ∨ ((True ∧ False) → (p5 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611543598696162590679956707196 : (((((True ∨ ((True → (True → (((p1 → ((p4 ∨ False) ∧ False)) ∧ (p3 → (False ∨ ((p2 ∨ p4) ∧ p5)))) ∨ p4))) ∧ p1)) → p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116015176514976494703786581838 : ((((True ∨ p3) → (p1 ∨ p1)) → (p3 → (((p3 ∨ True) → ((p2 ∨ (p4 → (((p4 ∨ p2) → p5) → p3))) ∧ False)) ∨ p1))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703831142009324647595700132843 : ((((((((p4 ∧ (p3 → p1)) ∨ True) ∧ p2) → p2) ∨ p5) → (((False → (((p2 ∨ p1) ∧ (True ∨ p5)) ∧ p4)) → (p4 ∨ True)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310383517782723329971291034989 : (p2 ∨ (((p4 → (p3 → (False ∨ (False ∧ p1)))) ∧ False) ∨ (((True ∨ p4) ∧ p1) → (((False ∧ p5) → (True ∨ (True ∧ p4))) → (p5 ∨ p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142476224128224778535554210061 : ((p5 ∧ ((p5 → ((p3 ∨ p1) ∧ p2)) → ((True ∨ (p1 → ((False → p3) → p4))) → (p1 → (p3 ∧ (p1 ∨ p2)))))) → ((True → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158967693044681897531676554755 : ((p3 ∨ ((p4 ∧ ((False ∨ (p5 ∧ ((p2 ∨ p1) ∧ (p1 ∧ (p1 ∨ (p4 → p4)))))) ∨ p4)) ∧ p1)) ∨ ((True ∨ (True → True)) ∨ (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647308345711768210180793997677 : ((((p4 → ((p5 ∨ (((((p3 ∧ (p3 ∨ True)) → True) → p1) ∨ (p1 ∧ (p3 ∧ (True ∧ (p5 → p1))))) ∧ p5)) ∧ (p3 ∧ p1))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111539551652045671299322286799 : (((((((((((False ∨ p3) ∧ p1) ∧ p2) ∧ p4) → True) → ((p3 → True) ∧ (p5 → False))) → (False → True)) → p2) ∧ True) ∨ True) ∨ (True ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700394719128156718994637484749 : ((((p5 ∧ (((True ∨ (False → p5)) ∧ False) → ((p2 → p4) → p4))) → (((p1 ∧ p3) ∨ ((p3 ∧ True) ∧ False)) ∨ (p3 ∧ (p2 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606936068618029646720173206327 : ((((((p2 → (((p4 ∨ (p2 ∧ p1)) → (((p5 ∧ (p3 ∧ p4)) → p2) ∧ p1)) → p5)) ∨ ((p2 ∨ True) → (True → p5))) ∧ False) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_658672283427863810872505556531 : ((((p4 ∨ (((((p4 ∨ p5) → True) → (p1 ∧ p5)) → (False → (((p2 ∧ (p2 → p3)) ∨ p2) ∨ (p5 → p5)))) → p5)) ∨ (p1 ∨ True)) ∨ p1) ∧ True) := by
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



