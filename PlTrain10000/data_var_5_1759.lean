variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189310635557496386399292996452 : (((p2 → p1) → ((((p1 → False) ∧ False) ∨ True) ∧ True)) ∧ (True ∨ (p2 ∧ (((p5 ∧ True) ∧ (((p2 → p5) ∨ p4) ∨ (p1 ∧ p4))) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309302228704618173263813540309 : (p2 ∨ (((((p4 ∨ p1) ∨ p5) ∨ (((p5 → (p4 ∨ ((p5 ∧ p3) → (((p5 ∨ p3) ∧ p5) ∧ True)))) ∧ False) ∧ p1)) ∧ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149886443048496610783035991907 : ((p2 ∨ ((p2 ∨ (p3 ∧ False)) ∧ ((p2 → (p1 ∧ (p1 → p5))) → ((False ∧ p2) ∨ (p3 ∧ (p4 → p2)))))) ∨ ((False ∧ p2) → (p1 ∧ p1))) := by
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346955359884948191854070887557 : (p3 → (((p2 ∨ True) → (((True ∨ ((p4 ∧ p5) ∧ (p2 → p2))) ∨ ((p3 → False) ∨ p3)) ∧ p4)) → ((False ∨ ((p2 → p3) ∧ True)) → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257730669769832949188753091840 : ((p3 ∨ p4) → ((((p2 ∧ (p2 → False)) ∨ (p2 ∧ (((((p4 ∨ False) → (p3 → True)) ∧ p1) ∧ p1) ∨ ((p3 → True) → p2)))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328651218869990060308636834193 : (True → (((p2 ∧ True) ∨ (((False ∨ ((p1 ∧ p1) → (p1 → False))) ∧ p2) → p5)) → (True ∧ ((p3 ∧ (p1 ∨ p5)) ∨ (p4 → (p4 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
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
theorem thm_5_vars_55456650294630782707797400264 : ((((p3 ∨ (True ∨ (p1 → p1))) → p1) → ((((p5 → p1) ∨ False) ∧ (((False ∨ True) ∨ (p5 ∨ (False ∧ p5))) ∨ (True ∧ True))) ∧ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (True ∨ (p1 → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (True ∨ (p1 → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54670540138095035325308151091 : ((((((p5 → p1) → (p3 ∨ p4)) ∧ p5) → True) → ((p3 ∨ p4) ∨ (p1 ∨ ((p2 ∨ ((p5 ∨ (p1 → p5)) ∧ p3)) → (p3 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760868759183243981136654194575 : (((p2 ∧ (p3 ∨ (True → ((False → ((p4 ∨ (False ∨ False)) ∨ (True ∧ True))) ∧ (((((p2 → (True → p5)) → p4) ∧ False) ∨ p3) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261618262080895389787353644940 : ((p5 → p5) → (((((((((p5 ∨ (p3 ∨ (True ∨ (p1 ∧ (p2 → False))))) → False) ∨ True) ∨ p1) → False) → False) ∨ p2) ∨ (p4 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173569274427167508504761946772 : ((((p1 ∧ True) ∨ (((False → (True ∧ p5)) ∧ ((False ∨ p2) ∧ p2)) ∨ False)) ∧ p3) → ((p4 ∨ ((p1 ∨ p5) ∨ (p2 → p2))) ∧ (p1 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h28 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174667784785675638860756286892 : (((True ∨ (p4 ∨ True)) ∧ (p3 ∧ ((p5 ∧ p4) → (p3 → (p3 ∨ (p3 ∨ p4)))))) → (True → ((((True ∧ p4) ∧ True) ∨ (p2 → False)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h4.left
      let h11 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809201682885649789144303854078 : (((p5 → (((((True → (((p5 ∨ True) ∨ (p5 → p1)) ∧ p5)) ∧ (True ∨ True)) → ((p2 ∨ (False → p5)) → p4)) ∨ (False ∨ p2)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659735010930915183873528060246 : ((((((p5 → False) → ((((p2 ∨ (p5 ∨ True)) → ((True ∧ (((p3 ∨ p4) ∨ p5) ∧ p1)) ∧ p3)) → p3) → p2)) ∧ p2) → (True ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179972790747688796010796443654 : ((((p3 ∨ (((p3 ∨ p1) → p5) ∧ p4)) → ((False ∨ p1) → p3)) ∨ p5) → ((p2 → False) ∨ (True ∧ (False → (p2 → (p3 ∧ (p5 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44594356859090671941924273084 : ((((((p1 ∧ p5) → (True ∧ (p2 ∨ p4))) ∧ p2) → (False ∨ (((p5 ∧ p5) ∨ (False ∧ (p1 ∧ (False ∧ (p3 ∨ False))))) ∨ p2))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32785958562180835887096998035 : ((p2 ∨ (p4 → ((((((p1 → True) ∨ ((True ∨ p1) → p5)) → True) → p5) → ((p5 ∧ p1) → p2)) ∨ ((False ∧ (False → False)) ∨ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51307150546811725498079785197 : (((p2 ∨ ((((((p1 → (True ∧ (p5 → p3))) → (p3 ∧ p4)) ∨ p5) ∨ p2) ∨ False) → p2)) ∨ (((p1 → (p3 ∧ False)) ∧ p2) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165659202419776062814238919143 : ((((True ∧ p5) ∧ (False ∨ (p2 → p4))) ∨ (p4 ∧ ((p2 → False) ∧ ((False ∨ p2) ∧ p5)))) ∨ (p2 ∨ ((True ∨ (p2 → p4)) ∨ (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216706154120353583381850449412 : ((((p2 ∧ p1) → p4) ∧ p4) → (((((p3 ∧ True) ∨ (p4 ∨ ((p2 → False) → p2))) → p3) ∨ False) ∨ (p2 → (False ∨ (p5 → (p1 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160000465847212163369055038091 : (((((p5 ∨ True) ∧ ((p4 ∧ p1) ∨ p5)) → ((p4 ∧ False) → (((p2 ∨ p4) ∨ p3) ∨ p1))) → False) → (p2 ∨ (((p5 ∨ p2) ∨ p3) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ True) ∧ ((p4 ∧ p1) ∨ p5)) → ((p4 ∧ False) → (((p2 ∨ p4) ∨ p3) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66218620900742257026401328027 : ((p5 ∨ ((p5 ∨ ((p1 ∧ p4) → (((p1 → (p5 ∨ p2)) ∧ False) ∧ p5))) → (p3 ∧ ((((False ∨ p5) ∨ (True ∧ p4)) ∨ p2) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313125627701084083815312971853 : (p3 ∨ ((((((True ∨ (p2 ∧ p5)) → p5) ∧ ((True ∨ (True ∧ p4)) ∧ ((p2 ∨ p5) → p4))) → p5) ∨ ((True ∨ (p4 ∧ p4)) ∨ False)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314966667793373555464263163155 : (p3 ∨ ((p4 ∨ (((False ∨ p4) ∧ (p4 ∨ p5)) → (False → False))) → ((False ∨ p3) ∨ ((True → (True → p1)) → ((p2 → (False → True)) ∨ p1))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743673506581697040937697671870 : ((((True ∧ p2) → ((p1 ∨ (((True → p5) → (False ∧ (p4 → (p2 → p3)))) ∨ (True ∨ p1))) → ((p2 → ((p5 → p5) → p5)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232665589091406749609987585944 : ((p1 ∧ (p2 ∧ p2)) → ((((((p3 → (p3 ∧ p3)) → p4) ∧ (p5 ∧ (p2 → ((False ∧ (p3 ∧ True)) ∨ p4)))) ∨ False) ∧ (False ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_215356125021569149555408315478 : ((p2 ∧ ((p5 ∨ p2) ∧ p1)) ∨ ((False → (p4 ∨ (p1 ∧ False))) → (((((p1 ∧ True) ∧ True) ∧ True) → (p4 ∨ p1)) ∨ ((p1 → p4) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64250662788498446847506855522 : ((False ∨ (p3 ∨ ((p3 ∧ (p3 ∧ ((p1 ∧ (p2 ∧ p3)) → ((False ∨ p3) → (((p3 ∨ p4) → ((p4 ∧ True) → False)) ∨ False))))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_822565630757308039945690264029 : ((((((p1 ∧ ((p4 ∧ True) ∧ (True ∨ (p1 ∨ p3)))) → True) → (p5 ∧ ((p2 → True) ∧ (p3 ∧ ((False ∧ (p3 ∧ p2)) ∧ p3))))) ∧ p5) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ ((p4 ∧ True) ∧ (True ∨ (p1 ∨ p3)))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232798119725951641751118001151 : ((p2 ∧ (p5 ∧ True)) → (((((True ∧ (((p1 ∧ p3) ∧ ((p4 → p1) ∨ (p1 ∨ ((False ∧ p1) → False)))) ∨ p4)) ∨ True) ∧ p2) ∨ True) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706266502582561023576739595385 : ((((p2 ∧ (p1 ∨ (((p3 ∧ True) ∧ False) ∨ p4))) ∧ ((((p1 ∨ p3) ∧ (p5 ∧ True)) ∨ p5) ∨ ((p5 → False) → ((True ∧ False) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57925255584374575933410066181 : (((True → (p3 ∧ False)) → ((((p5 ∨ p3) ∨ p5) ∨ (p1 → ((True → True) ∨ p3))) → (((p2 ∨ (p1 ∧ p2)) ∧ p5) ∧ (False → p5)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h6 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h7 := h1 h6
        -- We need to get the right conjuct of h7 based on <expert-advice>.
        let h8 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h11 := h1 h10
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h26 := h1 h25
        -- We need to get the right conjuct of h26 based on <expert-advice>.
        let h27 := h26.right
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h29 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h30
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- False on the left can always be used.
    apply False.elim h32
  -- Implications on the right can always be decomposed.
  intro h33
  -- False on the left can always be used.
  apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164757745737367894218427801861 : ((((p3 ∧ (p3 ∧ ((p2 → False) ∧ ((p4 ∨ p3) ∨ False)))) ∧ ((p5 ∧ p4) → p2)) ∨ True) ∨ ((((p1 ∧ p2) ∨ False) ∧ (p3 ∧ p2)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160976997936065003179234690289 : (((p5 ∨ (p2 → False)) ∧ (False ∨ (p3 ∨ ((True → ((p4 ∨ ((p3 → p1) ∨ False)) ∨ p1)) → p3)))) → (p1 ∨ (((p3 → False) → p1) ∨ p3))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : (True → ((p4 ∨ ((p3 → p1) ∨ False)) ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h12
          -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
          have h13 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h9, we can now drive its conclusion.
          let h14 := h9 h13
          -- False on the left can always be used.
          apply False.elim h14
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h10
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h16 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h17 := h9 h16
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h23
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h24 : (True → ((p4 ∨ ((p3 → p1) ∨ False)) ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h26
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h27 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h28 := h23 h27
          -- False on the left can always be used.
          apply False.elim h28
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h29 := h22 h24
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h30 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h31 := h23 h30
        -- False on the left can always be used.
        apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590152902423634737619398434412 : (((((((p3 ∨ (p1 ∨ p2)) ∨ (True ∨ (False ∨ p1))) ∨ (False ∧ (((((p5 ∧ p3) → p5) ∨ p5) → (p5 → True)) ∧ True))) → p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135720513173718592571544660588 : (((p3 → ((p3 ∨ ((p5 ∧ True) ∨ ((p5 ∨ p4) ∧ False))) ∧ (p3 → p4))) ∧ (p2 ∧ ((p5 → (p2 ∧ p3)) ∨ p3))) ∨ (False → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205672265052171630059051126100 : (((p2 ∨ p3) ∨ ((p5 → p2) → p4)) ∨ ((p1 ∧ False) ∨ ((p4 ∧ (True ∧ (p3 ∧ (p5 → (False → p2))))) → (p5 → ((True ∧ p1) ∨ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323557382029342057526990162230 : (p5 ∨ ((((p1 ∧ ((p3 ∧ ((p2 → ((True ∧ p1) ∨ (p3 → False))) → p4)) ∧ False)) → p3) ∧ ((False ∨ True) ∨ False)) → (p4 ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124511816472805209090416990535 : (((((p2 ∧ p4) → True) → (p3 ∧ p1)) ∧ (((p2 ∧ p1) → True) ∨ (((p5 → p2) ∨ ((False ∨ p4) ∧ p4)) → (p1 ∧ p4)))) → (p3 ∧ p3)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 ∧ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : ((p2 ∧ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h17
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h22 : ((p2 ∧ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h24 := h14 h22
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253967107689667332381269366673 : ((p1 ∧ p5) → ((((((True ∨ p4) → True) → (((p3 ∧ p2) ∧ p5) ∨ False)) ∨ (p3 ∨ p5)) ∨ (True ∧ ((True ∧ p2) ∧ (True ∨ p2)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327914342373946691553012701004 : (True → (((p3 ∧ (((p1 ∨ ((((False ∧ p1) ∨ p1) → p1) ∨ p3)) ∨ ((p4 ∧ True) ∧ p2)) ∨ (p2 ∨ (p4 → p5)))) ∧ p1) → (False ∨ True))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233079631489056983584585207967 : ((p4 ∧ (True → True)) → ((((False ∨ (p2 ∧ p1)) ∨ p2) ∧ p3) ∨ (p4 ∨ ((True ∧ ((False → p1) ∨ (p3 ∨ p1))) ∧ (False → (p3 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158177972816102695477825792520 : ((((p5 ∧ p2) → (p5 ∧ p5)) → (((True → False) ∧ (p3 ∧ (p4 ∨ p1))) ∧ ((p2 ∨ True) ∨ p3))) ∨ (((True → (True ∨ False)) → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117770828648511146875031156458 : ((p4 ∧ (((((((((p5 → True) ∨ p1) → ((p2 ∨ p3) ∧ False)) ∨ p5) ∧ True) ∨ p1) → p3) ∧ (p4 → True)) ∨ (p1 ∨ False))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617251281441352000347481315039 : (((((False ∨ ((False ∧ (p3 ∧ (False ∧ p4))) ∧ p1)) ∨ ((p3 → ((True ∨ ((((p3 → True) → p4) ∨ p3) ∨ p1)) ∧ p5)) ∨ p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251777445327421337152358387704 : ((p3 → p4) ∨ ((p1 ∨ (((p2 → (((p3 ∨ p1) ∧ ((p2 → False) → (True ∨ True))) ∨ False)) ∨ p1) ∨ (p3 → (p1 → (p1 → p1))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346293456876507448331269345365 : (p3 → (((((((((p1 ∧ p1) → p1) ∧ (True → p1)) → p2) ∧ p4) ∧ ((True ∨ (p2 → p4)) ∧ (p3 → p5))) → False) ∨ p3) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193095786816882921110496982107 : (((p5 ∧ ((p3 ∧ p1) → p1)) ∧ ((p5 ∧ True) ∧ p5)) → (True ∧ ((((p2 ∨ ((p3 ∨ True) ∨ (p3 ∧ True))) ∧ p5) → (p4 ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187802517971142902625115152021 : ((p3 → (p4 → ((((p2 → (True ∨ p2)) ∨ p5) ∧ p3) ∨ p2))) → (p4 → (True → (((p5 ∨ (p2 ∨ (p4 → True))) → (True ∧ p5)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184727117559968050608418646409 : (((True → ((p1 → p4) ∧ (p4 → p1))) → ((p1 ∧ False) ∨ p3)) ∨ ((((p1 → True) ∨ p2) → p3) ∨ (True ∨ (p2 ∨ (p4 ∧ (True ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234656571196638648931298541823 : ((p4 → (True ∧ p2)) → (((p4 → False) ∨ p2) ∨ ((p3 ∨ ((p2 ∨ ((p3 ∨ p5) ∧ p2)) → (p2 ∧ (p4 → ((False → p5) → True))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197764663435700296217594276795 : (((p1 ∨ (p5 ∨ True)) ∧ (p4 ∨ (p3 ∨ p3))) ∨ (True ∧ (((p5 ∧ ((p5 → (True → p3)) → p3)) → p2) → (True ∨ (p3 ∧ (p1 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59019697596686401910406043238 : (((p3 ∧ p5) ∨ ((p4 → ((True → (p4 → ((p1 → (p4 → True)) → p5))) ∨ ((p1 ∨ (p5 → p5)) ∨ (p4 ∨ p3)))) ∧ (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674059316242316856963283029165 : ((((p1 ∧ (p1 ∧ ((p4 → (p5 → p4)) ∧ (((p1 ∨ (p3 → p4)) ∨ p5) → (p3 ∧ ((False ∧ p1) ∧ False)))))) → ((False → p3) → p5)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 ∨ (p3 → p4)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187303109566799300039684025694 : ((p1 ∧ (((p5 → (p1 → (True ∧ False))) ∨ p3) ∧ (p4 ∨ p2))) → (((p5 → ((p3 → (((p3 ∨ True) → p3) ∨ p4)) → p3)) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244370015949058246100679741843 : ((False ∧ p1) ∨ ((((((False ∧ p4) ∨ (((p1 ∨ (True → (p2 ∨ False))) → p4) ∧ (p4 → p4))) ∧ p2) ∨ (p5 → (False → True))) ∨ False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_730791863973757626657876707966 : ((((p4 ∧ (p1 → p4)) → (((((False ∨ (p1 → True)) → (True → (((p4 ∧ p1) ∨ p4) ∨ ((p5 ∧ False) ∧ p5)))) ∨ p5) → p2) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672515256138408562060718360649 : (((((p2 → (((((False ∨ p2) ∨ (p1 → p3)) ∨ p4) → ((p3 ∧ (p1 → p2)) → p1)) ∧ (False ∧ p5))) → p4) → ((p1 → False) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734160967387824250357275995985 : ((((True ∨ p5) ∧ (p4 ∧ (((p5 → p4) → (((p3 ∨ p5) → True) ∨ p3)) ∧ ((False ∨ p2) ∧ (p5 ∧ (p3 ∧ ((p2 ∨ p4) → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264840297811883443298710346558 : (True ∧ ((p2 ∨ False) ∨ (((p2 → (p1 ∨ ((p2 → (False ∨ ((p3 ∧ True) ∧ (p3 ∧ p2)))) → ((False ∨ (False ∧ p5)) ∨ p3)))) ∧ p1) ∨ True))) := by
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
theorem thm_5_vars_134735154885754061140418361493 : ((((True ∨ p5) ∧ (((p3 ∨ p1) ∨ (False → ((p1 → p1) ∨ (p2 ∧ p2)))) ∨ (((p2 → p4) ∨ p5) ∧ True))) → False) ∨ ((p2 ∧ p5) → p5)) := by
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
theorem thm_5_vars_649541183445047612834012688721 : (((((p2 → (((p5 ∧ p3) ∧ ((p3 ∨ (p4 → (p1 → False))) ∨ True)) → (True ∧ ((p3 ∧ False) ∨ p3)))) ∧ (p5 → True)) ∧ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261338198863097910574349503909 : ((p5 → False) → ((((p2 ∨ (p1 ∧ (p1 ∨ True))) ∨ p3) ∨ (p3 ∨ p3)) ∨ ((((p3 ∧ False) → p3) ∨ p1) ∨ (p3 → ((p3 ∧ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180274578325101292945191557245 : (((p1 → (p3 → (False → ((p5 ∨ p5) → (p2 ∧ (p3 ∧ p5)))))) → p1) → (True ∧ ((p3 ∧ ((p3 ∨ p5) ∧ (p4 ∨ p4))) ∨ (p4 → p1)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p3 → (False → ((p5 ∨ p5) → (p2 ∧ (p3 ∧ p5)))))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597868569244661690024119246519 : ((((((p2 ∨ True) ∨ p5) ∧ (((((p1 ∧ p1) ∨ True) ∧ ((p1 ∨ (((p4 → p2) → p2) ∨ (True ∧ p1))) ∨ p3)) → p2) ∨ p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860000290061512913660741805726 : ((((((((p5 ∧ (p1 ∨ ((p5 ∨ True) ∨ (p5 → (p2 → True))))) ∨ p4) → (False ∨ p5)) ∧ (p4 → (p5 → p2))) ∨ (p3 → True)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ (p1 ∨ ((p5 ∨ True) ∨ (p5 → (p2 → True))))) ∨ p4) → (False ∨ p5)) ∧ (p4 → (p5 → p2))) ∨ (p3 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50264429483889181176421177239 : (((((((p5 → p1) ∨ p5) ∨ (((p1 ∧ p4) ∨ (False ∧ (p2 → p5))) ∨ p4)) → p3) ∧ (p3 → p5)) ∨ ((p5 ∧ p4) ∧ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677754082762883386625957438161 : (((((p5 ∧ ((((p4 → True) ∧ (p3 ∧ (False ∨ ((p3 ∧ (p5 ∧ p3)) ∧ True)))) ∧ False) → p2)) → p4) ∨ (((p4 ∧ p4) ∨ True) ∨ p4)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114330120705907023008632482067 : (((False ∧ (((((p3 ∨ ((True → p1) ∧ (p1 → p3))) ∨ (False ∧ False)) ∧ p5) ∧ p4) ∧ p4)) ∧ ((p5 → False) ∨ (p4 ∨ p1))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134071163022487248340881630870 : ((((((p4 ∨ p2) ∨ (((p1 ∧ (True ∧ p4)) ∧ ((p4 ∨ (True ∨ True)) → (p3 ∨ p1))) ∨ p5)) → p1) → p2) ∨ p5) ∨ (False → (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49087329939880818977558346695 : (((((((False → (p4 → False)) → (p3 → p1)) ∧ p3) ∨ ((p1 → (p1 ∨ p2)) → p2)) ∧ (p4 ∧ (p5 ∧ p5))) ∨ ((False ∧ p3) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3029488874151147791611000199 : ((p3 ∧ (p1 → p3)) → ((((p1 → True) ∨ (((True → (p2 ∨ (True ∧ True))) ∧ p4) → ((p2 ∨ (p3 ∨ p5)) → False))) → False) ∨ True)) := by
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
theorem thm_5_vars_181605130972965180786893683880 : ((p2 → (((p4 → p4) → (False → (((p5 ∨ False) → p3) → p1))) ∧ p2)) → ((((p1 → p2) ∧ ((p3 ∨ p3) → p4)) ∨ True) ∨ (p2 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317593361476777741409614421330 : (p4 ∨ ((((p1 ∧ (True → ((p2 ∨ p2) ∨ ((p1 → p5) ∨ p2)))) → ((True → (False ∨ True)) → (((p2 → p4) ∨ p5) ∧ False))) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317763549527260964443486922640 : (p4 ∨ (((p2 → (p3 → ((((p3 ∧ p5) → False) ∨ (p4 → (False → p1))) → (p2 → False)))) ∨ ((((True ∨ p1) → p2) ∧ True) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93896517957442509793713153705 : ((p1 ∧ (((((p1 ∨ False) ∨ False) → p3) ∧ (p2 → (p1 → (p2 ∨ p4)))) ∧ (False → (p3 ∨ ((p4 → (p1 → (p2 ∧ p5))) ∧ p3))))) → p3) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∨ False) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218346514225373542833559332972 : (((p1 → p5) ∨ (p1 → p2)) → (p2 → ((p2 ∨ (p3 ∨ ((True ∧ False) ∧ (False ∨ (True → (p1 → ((p1 → p1) → (p5 ∧ p4)))))))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95562863396146408712713040822 : ((p5 ∧ ((((((p1 ∨ (False ∨ (True ∨ p3))) → False) ∨ p3) → (((False ∧ False) ∨ False) ∨ True)) → False) ∧ (p3 ∨ (p1 → (p4 ∨ p1))))) → p1) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((((p1 ∨ (False ∨ (True ∨ p3))) → False) ∨ p3) → (((False ∧ False) ∨ False) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
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
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h7
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : ((((p1 ∨ (False ∨ (True ∨ p3))) → False) ∨ p3) → (((False ∧ False) ∨ False) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h13
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51129853904575619696399315376 : ((((p5 ∧ ((p1 ∧ p5) ∨ ((p4 ∨ ((((p5 → p1) ∧ p1) ∨ p5) ∧ True)) ∧ p3))) ∨ True) ∨ (((p1 → p2) ∧ (p5 ∨ p1)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139911679842282515729321597525 : ((((((p2 → ((p1 ∧ p5) → True)) ∨ False) ∨ (((p5 → p5) ∨ p4) ∨ p3)) → ((True ∧ False) ∧ False)) ∧ (True ∨ p5)) → (False ∨ (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 → ((p1 ∧ p5) → True)) ∨ False) ∨ (((p5 → p5) ∨ p4) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (((p2 → ((p1 ∧ p5) → True)) ∨ False) ∨ (((p5 → p5) ∨ p4) ∨ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h11
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184822610298901053865088057026 : (((((False ∨ p4) ∧ p2) → p1) → (False ∧ (p4 ∧ (p5 → p2)))) ∨ (((p4 ∨ p4) → (((p4 ∧ p3) → p4) ∨ ((p4 ∨ p5) ∧ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157472842073137527636289033303 : ((((p5 ∧ ((False ∧ ((p2 ∨ (p3 ∧ (p1 ∧ p2))) ∧ p4)) → (p5 ∧ p1))) → p1) ∨ (p2 ∨ True)) ∨ (False ∨ (False ∧ (p3 ∧ (p4 ∨ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244174551737206951105387481862 : ((True ∧ p4) ∨ (p4 ∨ ((((((False ∧ (p1 ∧ False)) ∧ (p5 ∨ (((p1 → True) → p1) ∧ p4))) ∨ True) ∨ p4) ∨ True) ∨ ((False → p5) ∧ p4)))) := by
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
theorem thm_5_vars_617298824457213531139852565045 : ((((((True → (p5 → ((p2 ∧ True) ∨ p4))) ∧ p1) → (False ∧ ((p4 ∧ ((False ∨ (p4 ∨ (True ∨ p1))) ∨ p1)) ∨ (p5 ∧ False)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_572994081118126373814057676006 : (((p1 → (p3 ∨ (((True ∧ ((p3 → p4) ∨ False)) ∨ (((True ∨ p2) → ((p1 → False) → False)) ∧ (((p4 ∨ p4) ∨ p4) ∧ p2))) ∨ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308574940146145129621063779706 : (p2 ∨ (((((False → p5) ∨ p2) → False) ∨ ((((False → (p2 → (p2 ∧ True))) ∨ p4) ∨ (p5 → (p1 → p3))) ∨ (False ∨ (p5 ∧ p1)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134934484731644441743234755308 : ((((p4 ∨ (((((p5 ∨ (False → (p5 ∨ ((p1 → p5) ∨ p5)))) → p5) ∧ p4) → p1) ∧ p4)) → p3) ∧ (False ∨ p2)) ∨ (p4 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740446919710484505800556133922 : ((((p1 ∨ p4) ∨ ((((((p5 ∧ p5) ∧ (p1 → p4)) → p5) ∨ p1) → False) ∧ (p3 ∧ ((((False ∨ (p2 ∧ p3)) → True) → p3) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324029445600296317867310149358 : (p5 ∨ (((p3 ∨ True) → ((p1 ∧ (False ∧ (((p1 ∧ p4) → p4) → p4))) ∧ p2)) → ((((p1 ∨ ((p5 ∧ p2) ∨ p1)) ∧ p2) ∨ p2) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310318000085051699667164605223 : (p2 ∨ ((((((p5 ∨ False) → False) ∧ (False ∨ True)) ∨ p5) ∧ True) → ((((True ∧ p5) ∨ (p1 ∧ p4)) → ((False ∧ False) ∧ False)) ∨ (True ∨ p2)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53134824535703105184572221824 : ((((((False ∨ p2) ∨ p1) ∧ ((p2 ∧ (p1 ∨ p3)) → True)) ∧ p1) ∨ (((p1 ∨ (False → ((p4 → (False ∨ p1)) ∧ p2))) → p1) → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (False → ((p4 → (False ∨ p1)) ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219393334981561362672894026057 : ((p3 ∨ (p5 ∧ (p5 ∨ p4))) → (p5 ∨ ((p2 ∨ p2) → ((p1 ∧ ((p1 ∧ True) → (p5 ∨ (True ∧ ((p1 → False) → p5))))) ∨ (p5 ∨ True))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103867023348517723611066278333 : ((((((True ∨ p5) ∨ (p3 ∧ True)) → False) ∧ (False ∨ (((p5 → p5) ∧ p2) → (p3 → (p1 ∧ (p2 ∨ (True → p3))))))) → p2) ∧ (p4 → True)) := by
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
    have h6 : ((True ∨ p5) ∨ (p3 ∧ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134370087386364252069211392327 : (((p2 ∨ (((False ∨ ((p5 ∧ p2) → p3)) ∨ (p3 ∨ (p1 ∨ p5))) ∧ (((False ∨ (True ∨ False)) → True) ∨ True))) ∨ p2) ∨ (p3 → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703272975821477026422515582132 : ((((p3 ∧ (((p2 ∨ False) ∧ p2) → ((p2 ∨ False) → p2))) ∨ (p4 → (p3 ∨ (((True → (p3 ∧ ((p4 ∧ False) ∧ True))) ∧ p3) → p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137962273227391363960419168710 : ((p5 ∨ ((True ∧ (((p1 ∧ p3) → (((p2 ∧ (p2 ∨ (p2 ∨ p4))) ∧ True) ∧ p1)) ∧ (p4 ∨ p5))) ∨ (p5 ∨ True))) ∨ ((p4 ∧ p1) ∧ p2)) := by
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
theorem thm_5_vars_185626730095645059868002338563 : ((True → (False ∧ (((p1 ∨ False) ∧ p1) ∨ (p2 ∨ (False ∧ p3))))) ∨ ((((True ∧ p5) ∨ (((p1 ∨ p1) ∧ (True ∨ p4)) ∨ True)) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193554571571777889013976906023 : (((p5 ∧ True) → ((p5 ∧ ((p3 ∧ False) → p4)) ∨ p4)) → ((p5 → p3) ∨ ((p5 ∨ ((p5 ∧ (True ∧ (True ∧ p4))) → False)) ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693364916030240578423122972386 : ((((p1 → (((p2 ∨ (p1 → p5)) → p3) → (p4 ∧ ((True ∨ p3) → p5)))) ∧ (False → ((p5 ∧ (((True ∨ p5) → p2) ∨ p2)) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677996647603168716592192748108 : (((((((((p3 ∨ True) → True) ∨ ((p3 ∧ p2) ∨ True)) ∨ (True → p1)) → p3) ∧ (p5 ∨ (p1 → p5))) ∨ (((p4 → p5) ∨ True) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



