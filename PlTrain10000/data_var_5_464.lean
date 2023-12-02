variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346774823111207877804247377902 : (p3 → (((((p4 ∧ (((True → p1) ∧ p1) → p2)) ∧ (((p2 ∧ p2) → p5) → False)) → p1) ∧ (True ∨ p5)) ∨ ((p3 → False) → (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158570611158631770372732446874 : ((True ∧ ((p3 → ((False ∧ ((False ∧ p5) ∧ (p4 → False))) ∧ False)) ∨ (p2 ∧ ((True ∧ p2) → p2)))) ∨ (False ∨ (p4 ∨ (p5 → (p5 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660439833605544961115591113565 : ((((((((p3 → (p4 → (True ∧ ((False → (p1 ∨ False)) ∧ (p4 ∧ p2))))) ∧ (p5 → (True ∧ p3))) → False) ∧ p2) → p5) → (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_827723589419513127046733263348 : ((((p2 ∧ ((((False → (False ∨ ((p2 → p3) ∧ True))) → False) ∧ ((p1 → ((p2 → p2) → (p3 ∧ (p3 ∨ False)))) ∨ True)) ∨ p5)) ∧ p2) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (False → (False ∨ ((p2 → p3) ∧ True))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h14 : (False → (False ∨ ((p2 → p3) ∧ True))) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h14
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62525924871713625152533025799 : ((p3 ∧ (p5 ∧ (p1 ∨ ((p5 ∨ (p4 ∧ ((True ∨ (((((False ∨ p2) → p4) ∨ False) ∧ (p5 ∨ p1)) → (p5 → p4))) ∨ True))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213277338533521806733823616921 : ((((False → True) → p2) ∧ p5) ∨ (((True → p5) → False) ∨ (((p3 → ((((False ∧ p5) ∨ True) ∧ p5) → p4)) ∧ (p4 ∧ (False ∧ True))) → False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751920527031937881264834545834 : (((True ∧ (p3 ∨ (((((p1 → p3) ∨ p1) → (((p1 ∨ p2) → p4) → False)) ∧ ((False ∨ (p3 → p5)) ∧ p1)) ∨ (p3 → (p4 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135733878800954058843877161493 : (((((p1 → True) ∧ ((p1 → p1) → ((p4 ∧ p2) → (True → p1)))) → p4) ∨ ((p1 ∧ ((p1 → True) ∧ p2)) ∧ True)) ∨ ((True → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47165068091650487535836165033 : ((((((p2 → (p4 ∨ False)) → p4) → ((((p4 ∨ True) ∨ p4) ∨ p1) ∨ p3)) ∧ ((p4 ∨ p5) ∧ ((True → False) → p2))) ∨ (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747125938726755673991649752379 : ((((p5 ∨ True) → ((p1 ∨ (p2 ∨ ((True ∧ p4) ∨ ((p5 ∧ False) → ((((p2 → (False ∨ True)) ∨ True) ∨ (p1 ∨ p3)) ∧ False))))) ∨ False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205040873764473747889832788404 : (((True → ((False → True) ∨ p2)) → p2) ∨ (((False ∧ (False ∧ (((((p3 ∧ p3) ∧ False) → p2) ∨ p5) ∨ False))) ∧ p2) ∨ (True ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51836084390683521262112948810 : ((((((True ∧ (p5 ∧ (p5 → p3))) → (p5 ∧ ((p1 ∧ False) ∨ p5))) ∧ False) ∧ p4) ∨ ((((False ∨ p1) ∨ False) ∧ p4) ∨ (True ∧ True))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66697095675002383362952091114 : ((True → ((p5 ∧ (p5 ∨ False)) ∨ (p2 ∨ ((p4 ∧ (((p3 ∨ True) → True) ∨ (((p3 ∨ p4) ∧ (True ∨ p4)) ∨ False))) ∧ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119052576359263652342374978486 : ((p1 → ((p5 ∧ ((((p3 ∨ p1) ∨ p3) → (p2 ∨ (p1 ∧ p5))) → (((p1 ∧ p5) ∧ p3) ∨ (p2 → (p2 → False))))) ∨ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760791173605458027041162265840 : (((p2 ∧ (p1 ∨ (p1 → ((p2 ∨ False) ∨ ((p1 ∨ (p1 ∧ (((p4 ∧ p4) ∧ (p2 → ((p3 → (p4 ∧ p1)) → p5))) ∨ True))) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56840361202644026934745873320 : ((((p5 → p1) → True) ∧ ((((p2 → (p2 → p2)) ∨ (p3 ∧ ((p5 → p3) → (p2 ∨ (p4 → p4))))) → p1) → (p2 ∧ (p1 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208836293055010544605503883112 : ((p3 ∧ (True ∨ ((p1 ∨ True) → True))) → (((((True → (p5 ∧ p5)) ∧ p3) → True) → (True ∧ False)) ∨ ((p3 ∧ p5) ∨ (p1 → (p2 → p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
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
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760579143636658915963420220852 : (((p2 ∧ (p3 ∧ (((True ∧ ((False ∨ True) → p2)) ∨ p2) → ((((((True ∨ p5) ∧ (p2 ∧ True)) ∧ p2) → p2) → (p4 ∧ p5)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232721768990192496216238601539 : ((p1 ∧ (p5 ∨ p2)) → (((p4 ∨ (p3 → p1)) ∧ (p1 → ((p3 ∨ ((p1 → p3) ∨ p3)) → ((False ∨ ((p3 ∨ True) ∧ p2)) ∨ p1)))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- One of the premise coincides with the conclusion.
    exact h26
  case inr h29 =>
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323475517934469621495738680928 : (p5 ∨ ((((((False ∨ True) → ((p5 → (p2 ∧ p3)) → p2)) ∨ ((True ∧ True) → p4)) ∧ (p3 → (False ∧ p3))) ∨ True) ∨ ((p4 → p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47244199480660232874808954361 : ((((((p5 ∧ p5) → (p3 ∨ p2)) ∨ p1) ∧ (((True → p2) ∧ (((p4 ∧ (True ∧ False)) → (p4 ∨ p4)) ∧ False)) ∧ p5)) ∨ (p4 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48774343053115875295110900209 : ((((p1 ∧ p5) → (((p4 ∨ False) ∨ p1) ∧ ((((False ∨ p3) → (False ∧ True)) → ((p2 → p4) → False)) ∨ p1))) ∧ (True → (True ∨ p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115374444311719987626068257237 : (((((False → (p2 ∨ p3)) → p1) ∨ (False → p1)) ∧ ((p1 ∨ ((p4 → p4) ∧ (p3 → (((False → False) ∧ p5) ∨ p5)))) → False)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52094550296786826531433668630 : ((((((((p2 ∧ True) → p4) ∨ p4) → p5) ∧ ((p1 → p2) ∨ (p3 → False))) ∨ p3) → (p1 ∧ (p3 ∨ (((p2 ∨ p3) → True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347015108241393666491847562572 : (p3 → (((False ∨ (((p4 ∧ True) ∧ False) ∧ p2)) ∧ (p1 ∧ (p1 ∧ (False ∧ (p2 ∨ p2))))) ∨ ((((p3 ∨ True) ∧ True) ∧ p3) → (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65383124995873972966690944748 : ((p3 ∨ ((False ∧ (p2 ∨ ((False ∨ (p4 ∧ p2)) ∨ False))) ∨ (((p1 ∧ p3) ∧ ((p1 ∧ p4) ∨ False)) → ((p5 ∨ True) → (p4 ∧ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204550919345883630865378787560 : ((((p4 ∨ (p1 → p5)) → p5) ∨ p1) ∨ ((p4 ∧ ((p2 ∧ ((p3 → p5) → (p2 → False))) ∧ (True ∧ (True ∨ (p4 → True))))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658188025480285014380478640877 : ((((p4 ∧ (p3 → ((((p4 ∧ ((((p3 ∨ True) ∧ ((p1 ∧ (p1 ∧ False)) ∨ p5)) ∨ p3) ∧ True)) ∨ p3) → p3) → False))) ∨ (True ∨ p2)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_114849535696101005368217778089 : ((((True → (((p3 ∧ p5) ∨ p2) → (p3 ∨ (p4 ∨ (False ∧ True))))) ∨ p5) ∨ ((p5 ∨ ((False ∧ (p1 → False)) → p1)) ∨ p4)) ∨ (p3 ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41765638197445353667295437277 : ((((False ∧ ((p2 → p5) ∧ p2)) ∨ (((p1 ∨ p5) → (((p1 ∧ p3) ∨ (p4 ∧ p4)) ∧ (p2 ∨ (p3 → p2)))) ∨ (p2 ∨ p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140433481816813314301996752155 : ((((((False ∧ False) → (p1 → p3)) → ((False → p1) ∧ p4)) ∨ (((p2 → p3) → p1) ∧ p1)) → ((p4 ∨ p2) ∨ False)) → (p4 ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668543419962227623077410271832 : (((((((p1 ∧ p1) → (p2 → True)) ∧ (p2 ∨ ((p5 → (p1 ∨ (p1 ∨ (p1 ∧ p4)))) → (False ∨ p4)))) ∧ p3) ∨ (False ∧ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41619323914144204260256783337 : (((((True → (True ∨ ((p1 ∧ p3) ∧ p2))) ∧ p3) → (p5 ∨ ((((False → ((False ∨ p2) ∧ p5)) → p5) ∧ False) ∨ (p1 → True)))) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166550649958110269059342135632 : ((p5 ∨ ((p2 ∨ ((p1 ∧ False) ∨ ((p5 ∧ p1) ∧ p2))) ∨ (((False ∨ p5) ∧ p4) ∧ False))) ∨ ((False → (p3 ∧ p5)) ∨ (p2 ∧ (p2 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779683469763705990468408527482 : (((p2 ∨ ((((((p2 → (True ∨ ((True ∨ ((p2 → False) ∨ (((p1 ∧ p2) ∨ p4) ∨ p3))) ∧ p2))) ∧ True) ∧ p5) ∧ False) → p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105564136784593754218514142545 : ((((p5 ∨ ((((p1 ∧ (p1 → p2)) ∨ p5) → p3) ∧ p4)) ∨ ((False ∧ (True ∨ p1)) ∧ p4)) → ((p3 ∧ p4) → (p2 ∨ True))) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642132451480597595054812795730 : ((((True ∧ ((p2 ∨ (False ∧ (False → ((p5 ∨ p3) ∨ p5)))) ∧ ((True ∧ p1) ∨ ((p5 → p5) ∨ (((p3 ∨ False) ∨ p2) ∨ p3))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117427379398975784137984866973 : ((p1 ∧ ((((((p2 → False) ∧ True) ∨ ((((True → p5) → p5) → False) → p3)) ∨ p1) ∨ p1) ∧ (((p2 ∧ p5) → p2) → False))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245240424435186235118209511976 : ((p2 ∧ p1) ∨ ((True ∧ (p4 → ((((p3 → (p3 ∨ (p1 ∨ p5))) ∨ True) → p2) ∨ (p5 → p5)))) ∧ (((p3 → p2) → p4) ∨ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206253328808028866711669942067 : ((False ∨ ((p2 → (p4 ∨ p5)) ∨ p2)) ∨ (((((p2 ∧ ((p1 → p3) ∧ p3)) ∨ (p1 → (p4 → p4))) ∧ True) ∨ p4) ∨ (p1 → (p1 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672433397402094556623785868366 : ((((((p2 → True) ∨ ((((p3 ∨ p1) ∨ ((True ∨ False) ∨ (True → p4))) → (p3 → p3)) ∨ (True ∨ p5))) → p5) → (p3 ∨ (p1 ∨ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → True) ∨ ((((p3 ∨ p1) ∨ ((True ∨ False) ∨ (True → p4))) → (p3 → p3)) ∨ (True ∨ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299092839058423858707593121599 : (False ∨ (((((p5 ∨ p5) ∨ ((p5 ∧ (p3 → ((False → (False → p2)) ∨ False))) ∨ (True ∨ (p4 ∨ (False ∧ False))))) ∧ (p4 → p2)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45445926433240587845452810032 : (((True ∨ ((p3 ∧ (p3 ∨ p1)) ∧ (((p4 → (p3 → True)) → (((((p3 → p2) ∧ p2) → p2) → (p3 → p2)) ∧ p5)) ∨ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40235012242057761046886922038 : ((((p3 ∧ ((p1 ∧ (((p5 ∨ (((p3 → (p3 ∧ False)) ∧ (p5 → True)) ∧ (p5 ∧ p3))) ∨ (True → p2)) ∨ False)) ∧ p1)) ∧ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181194619042098054737283533014 : ((p2 ∧ (((((p3 ∨ p3) ∨ (p3 ∨ p1)) ∨ p3) ∨ (True → p4)) ∧ True)) → (p1 ∨ ((False ∧ (((True ∨ p5) ∨ (p2 ∧ p1)) ∨ p2)) → False))) := by
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
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- False on the left can always be used.
          apply False.elim h11
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
      case inr h17 =>
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
          -- False on the left can always be used.
          apply False.elim h20
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h25
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728654232359643707710719685965 : ((((p5 → (False ∧ p4)) ∨ (p4 → ((True → ((p3 ∨ (p5 → ((p5 ∧ p1) ∨ ((True ∧ p4) → (p4 ∧ True))))) ∧ False)) → (True ∧ p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636989788099720306738329869845 : (((((((p1 ∧ (p4 → p1)) → p3) ∧ (((False ∧ p3) ∧ p1) → True)) ∧ (((p3 → (((False → p2) → p2) → p2)) ∨ True) ∨ p2)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161857661338553781852955838826 : ((True → (p5 ∨ ((((p5 → p4) → (p3 ∧ ((True ∨ True) ∨ p3))) → p1) ∨ (p5 → (p1 ∧ p4))))) → (p1 ∨ (((p3 ∧ p5) ∧ p3) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49498965457600208428321276946 : ((((p2 ∧ ((p3 → ((((p3 → p2) → p1) → ((p1 → p4) ∧ p3)) ∧ ((p5 → p5) ∧ p4))) ∧ p2)) → p2) → (p2 → (p1 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137368815011791606596718239947 : ((p3 ∧ (((False ∨ p5) ∨ (p4 ∧ ((p2 ∧ ((True ∧ True) ∨ (p4 ∧ p2))) → (p4 → (p3 → p3))))) → (p2 ∨ p5))) ∨ (p1 → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638657368635488001472613433038 : ((((((False ∧ (p4 → (p2 ∨ p1))) ∨ p4) → (p4 ∧ (((((False → (p3 → (p1 ∧ p1))) ∧ p1) → p4) → p4) → (True → True)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613232286266276940043553788855 : ((((((((p2 → True) → ((True ∨ ((p3 ∨ True) ∨ p5)) ∧ p2)) ∧ p3) → (((p5 ∧ p1) → p4) ∨ (True ∨ False))) → (True ∧ p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324547670862622874582594706673 : (p5 ∨ ((True ∧ ((p3 ∧ p3) ∧ p1)) → ((((False ∧ (p1 → (p5 ∨ (p4 ∨ True)))) ∧ (True ∧ True)) ∧ (p2 ∨ True)) ∨ ((True ∨ True) → p1)))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339725924629103026443121335015 : (p1 → (p4 ∨ ((((p3 ∧ True) ∧ p1) ∨ (p5 ∨ ((((((True → ((p1 ∨ p2) ∨ (p1 ∧ p3))) → p4) ∧ True) → p2) ∧ p3) ∨ True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172436413307257122788768561804 : (((p4 → ((p1 ∨ p2) ∨ p2)) ∧ ((((False ∧ p5) ∨ False) ∨ p2) ∧ (p3 ∨ p2))) ∨ ((True ∧ (((p2 ∧ True) → (False → p5)) ∨ p5)) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304856278421350154022222827856 : (p1 ∨ (((((True → False) ∨ (p4 ∧ False)) → p4) → ((((True ∧ (p5 ∨ p3)) ∧ (((True ∧ p4) → p2) → p4)) ∨ False) ∧ False)) → (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → False) ∨ (p4 ∧ False)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1563499850156690219025781132 : ((True → (p1 → ((p1 → False) ∨ ((False → (p2 ∨ (True ∨ (((True ∧ p1) ∨ p3) → True)))) → ((p2 ∧ False) ∨ p5))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172082727915256111193480607984 : ((((p1 ∨ (p1 → p4)) ∧ (((p2 ∧ (False ∨ p1)) → p3) ∧ p1)) → (p5 ∧ p5)) ∨ (((p1 ∧ p2) ∨ ((False ∨ p1) → p2)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252403330757363784961118211858 : ((p5 → False) ∨ ((p3 → ((p2 ∧ (p3 ∧ True)) → (((p2 ∨ (p2 ∨ True)) ∧ (((p2 ∧ p2) ∨ True) → p3)) → p5))) ∨ ((p4 ∧ p3) → p4))) := by
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
theorem thm_5_vars_396011120380456046082098195581 : ((((p4 ∧ ((((p3 → (((p1 ∨ p1) → (p5 ∨ p2)) ∧ (p4 ∨ (p1 ∧ p4)))) ∧ (((p3 ∧ p5) → p4) → p2)) ∨ p3) ∧ p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_259625997625934433156294047094 : ((p1 → False) → ((((p1 ∧ (p2 ∧ ((p4 ∧ p5) ∧ (False → (False → p1))))) → True) → ((p3 → p1) ∧ (p1 ∨ (p3 ∧ False)))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258423116184586420338426705383 : ((p5 ∨ p1) → (((((p1 ∧ (p5 ∧ (False → p5))) ∨ p1) ∨ p5) → False) ∨ ((True ∨ True) ∨ ((False ∨ ((False → p2) → p2)) ∨ (p2 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166069611254654089912744489176 : (((True ∨ False) → ((((p4 ∧ (((p4 ∨ (False → p4)) ∧ p1) ∧ p1)) ∧ p4) ∨ p1) ∨ p2)) ∨ (True ∨ (((p1 ∨ False) → (p5 ∧ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199007687951684654213863262332 : (((((p3 → (p5 ∧ True)) ∨ True) ∧ True) ∧ p5) → ((((False ∨ (p1 ∧ p3)) ∧ (False → (p3 → p5))) ∧ (p4 → (p4 ∧ (p4 ∨ p2)))) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171552938440274926274391544650 : ((((((p5 ∨ ((p3 ∧ p3) ∨ p3)) ∨ p2) ∧ (False ∨ (p2 ∨ p4))) → p5) ∨ False) ∨ (True ∨ ((p5 ∧ p4) ∧ ((False ∨ (False → p5)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184648076162755963207723464988 : ((((p3 → (p5 → (p4 ∨ p1))) ∧ p2) ∨ (p3 ∧ (p4 → p2))) ∨ (False → ((False ∧ ((False ∧ (p3 ∨ (p4 ∧ (p5 → True)))) ∧ False)) → p5))) := by
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
theorem thm_5_vars_174099416338622318956057486839 : (((((p5 ∧ False) ∧ p3) ∨ ((False → (p2 ∨ (p2 ∧ p1))) → p2)) ∧ (p3 ∨ p2)) → ((p4 ∨ p5) ∨ (((p4 → True) ∧ p4) ∨ (False → p4)))) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139581164739954134298551584449 : (((((((p2 ∧ p5) → True) ∧ (True ∨ (p5 ∨ p1))) ∧ (p3 ∨ (p1 ∧ (p1 → p3)))) → (p4 ∧ (False ∨ p3))) → False) → ((True → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137952712446600965484981729344 : ((p5 ∨ ((p2 → ((p2 → p3) → (((True → (((p4 ∧ p1) ∨ p2) ∧ (p1 → (False → p2)))) ∨ True) → p5))) ∨ False)) ∨ (p1 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57574014110621899061662372800 : ((((p1 ∨ p5) ∧ p5) → ((True → p5) → ((p3 → (False ∨ (p3 ∧ (p3 ∧ ((((p1 ∨ (p3 → p5)) ∨ p1) ∨ p4) → p4))))) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149112733281137453077907400083 : (((True ∧ p1) ∧ (((True ∨ (p2 → p2)) ∧ p2) ∨ ((p1 ∨ p2) ∧ (p1 ∧ ((p4 ∨ (p1 ∨ p5)) → p4))))) ∨ (p5 → (False → (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113552448127609307408397934556 : (((((True → p1) → p5) → ((False ∨ ((p4 ∧ ((True → (p5 ∨ p1)) ∨ ((False ∧ p2) ∨ False))) → p1)) → p5)) ∨ (True → p5)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21463052939448468028760727424 : ((((p4 ∨ ((p1 → p4) ∨ (p1 ∧ p4))) ∨ (p4 → p5)) ∨ (((False ∧ (p2 ∧ p5)) ∧ True) ∨ ((p3 ∧ p5) ∨ ((p1 ∨ p2) → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_191431539944519737830462588554 : (((p3 ∨ p1) → ((p5 → p4) ∧ ((p2 ∨ p3) ∧ False))) ∨ (True → (p1 ∨ ((((True ∧ p3) ∧ p2) → (p1 ∨ ((p2 → p3) ∨ p3))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118167340866655910817527223166 : ((False ∨ ((p2 ∧ p3) ∨ (p2 → ((True ∨ (((((True → p2) → p3) → p3) ∨ False) ∨ p4)) ∧ ((p3 ∨ (p5 → p1)) ∨ p4))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56460870662572706477073956386 : ((((False ∧ p5) → (True ∨ p5)) → (((p3 ∧ p3) → (((p2 ∧ p4) ∧ ((True ∨ p5) ∨ (True ∨ (p3 → p5)))) → True)) → (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187068542195798208055346588739 : (((p3 ∨ False) ∧ ((p4 ∨ p5) ∧ (((p2 ∨ p2) → p3) ∨ p5))) → (((p2 ∨ p5) → (p3 ∧ p2)) ∨ (False ∨ ((True → True) ∨ (p3 → p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217477875405047516278102021631 : ((((p2 ∧ p2) ∧ False) → p4) → (p3 ∨ ((p4 → (((((False → True) → p5) ∨ ((True ∧ (p3 ∨ p4)) ∨ False)) → p5) → p3)) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_689011296724459028120364345047 : (((((((((True ∧ (True ∧ p2)) → (p3 ∨ p1)) → p1) ∨ p1) ∧ (p2 → p3)) ∨ True) ∨ ((p4 ∧ (p4 → (True ∧ True))) ∨ (p4 → False))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_190470037067663664074867652567 : (((((p4 ∨ (False ∧ True)) ∧ (False → True)) ∧ p4) → p1) ∨ ((((True ∨ p1) → ((((p3 → (False → False)) ∧ p3) ∨ p3) ∨ True)) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p1) → ((((p3 → (False → False)) ∧ p3) ∨ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167400996047526492098103268212 : ((((p5 ∨ p1) ∨ (p4 ∨ ((p1 ∧ ((((p3 ∨ p4) ∧ p4) → p4) ∨ False)) → True))) → False) → (p4 ∧ (((p3 ∧ p2) ∨ p4) ∨ (p3 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p1) ∨ (p4 ∨ ((p1 ∧ ((((p3 ∨ p4) ∧ p4) → p4) ∨ False)) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 ∨ p1) ∨ (p4 ∨ ((p1 ∧ ((((p3 ∨ p4) ∧ p4) → p4) ∨ False)) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178758584320731999110699457669 : ((((p2 ∨ True) ∨ False) ∧ (p3 ∨ (((p3 ∧ p2) ∨ p4) ∨ (True → p5)))) ∨ (p1 ∨ (p3 ∨ (((p4 → False) → p2) → (p4 → (p5 → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58165199415109486124678557948 : (((p3 ∧ False) ∧ ((((((p4 ∨ False) → p2) → p5) ∧ (((True ∨ p4) ∨ p4) ∨ True)) ∨ ((p3 → True) → (p5 → p3))) → (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719739731050718288549224623688 : ((((p1 → ((False ∨ p4) ∧ p2)) ∨ ((p3 ∧ p1) ∧ (((p1 ∧ ((False → False) ∨ ((p1 ∨ p3) ∧ p3))) ∧ (p5 ∨ p2)) ∧ (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659519503789310246924548552559 : (((((((p4 → (p4 → (False ∨ (p1 ∨ ((False → ((p1 → p3) → (False ∨ p3))) → p3))))) → p3) ∨ (p1 → p1)) ∧ p3) → (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356894537209364427096109072937 : (p5 → ((((p1 ∧ True) ∨ p3) → p4) → (((((True ∧ (((p3 ∨ (p4 ∨ p2)) ∧ False) → p1)) ∧ (p4 ∨ p5)) → p2) ∧ (p4 ∧ p4)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : ((True ∧ (((p3 ∨ (p4 ∨ p2)) ∧ False) → p1)) ∧ (p4 ∨ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h16 := h4 h8
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115352057974774628840116964942 : (((((p1 ∧ (True ∨ False)) → (p1 → p3)) ∧ p1) ∧ ((((p1 ∧ p2) ∧ ((True → p4) ∧ True)) ∧ p2) ∧ ((True ∧ True) → False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226386996660770818372573738904 : (((True → p5) ∨ p5) ∨ ((((p5 ∨ p3) → (p3 ∧ p4)) ∨ ((((((False ∧ p1) ∨ p3) → False) ∨ False) ∨ (p2 → (p1 ∧ p3))) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_951443396941665006710468997195 : ((((p5 ∨ (p4 ∨ p4)) ∧ ((p1 → (p3 → ((p4 ∧ (p1 → p1)) ∨ (False → p3)))) → (((True ∨ False) ∨ (p4 ∨ p3)) ∧ (p5 ∧ False)))) → False) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (p3 → ((p4 ∧ (p1 → p1)) ∨ (False → p3)))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (p1 → (p3 → ((p4 ∧ (p1 → p1)) ∨ (False → p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h14
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : (p1 → (p3 → ((p4 ∧ (p1 → p1)) ∨ (False → p3)))) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h22
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670891162170080872436843177177 : ((((p3 ∧ (((((True ∧ (p2 → True)) → False) ∧ (p4 ∧ ((p5 → False) ∨ p2))) ∨ p1) → (True ∧ (p3 ∧ True)))) ∨ ((True → p2) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_158238322007115389901506629915 : ((((p1 ∧ p2) ∧ p3) ∨ ((p1 → p2) ∧ (((False ∨ False) ∨ (False ∨ p4)) → ((False ∨ p5) ∧ p2)))) ∨ (p3 → (True ∧ (True ∧ (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53640040820511654864986680805 : (((((p1 ∨ p1) ∨ p1) ∧ ((p3 ∨ (p4 → p1)) ∧ p4)) ∧ ((p2 ∨ ((((p3 ∧ p3) → p3) ∨ (p2 → (False ∧ p1))) ∧ p4)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137065643277962517066966718985 : (((p3 → p2) → (p4 ∨ (p3 ∨ ((p3 ∨ p1) ∨ (((p3 ∨ False) ∨ True) → (p3 ∧ (p4 → ((p3 ∧ p5) ∧ True)))))))) ∨ (p2 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53930252195170042797744011447 : (((p5 ∨ ((p5 ∧ False) ∨ ((False ∧ (p5 ∧ False)) ∧ p1))) ∨ (p3 → ((False → (p2 ∧ ((p5 ∧ p1) ∧ (p4 ∨ (p3 ∧ p3))))) ∨ False))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147591036523816321860048397402 : ((((((p3 → True) ∧ (p5 ∨ (True → ((p2 ∨ (False ∧ (p2 → (p1 ∧ p3)))) → p1)))) ∨ p2) ∨ True) → p3) ∨ ((p1 ∧ (p2 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355605343978639925880205536396 : (p5 → (((p2 ∧ p4) ∨ (p4 ∨ ((((False ∨ ((p3 ∧ (p4 ∧ p1)) → p3)) ∧ (p5 ∧ (p5 ∨ p3))) → (True ∧ p2)) ∧ False))) ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259429516520448232926477887937 : ((False → p4) → ((p3 ∨ ((p5 ∧ (p5 ∧ ((p4 → ((p3 ∧ p4) → (((False → p5) ∧ p1) ∧ ((False ∧ True) → False)))) ∧ p2))) ∨ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111392453699893451123877758210 : (((p1 ∨ (((p5 ∨ ((p1 ∧ p5) → (True ∨ ((((p5 ∨ p1) → p1) ∨ p3) ∨ ((p2 ∧ p1) → False))))) ∨ p2) → p5)) ∧ p1) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178303948213381450708633855030 : (((((p3 ∧ (p1 → (p5 → (p3 → True)))) → p5) ∧ p5) ∨ (p1 ∨ True)) ∨ (((p4 → (p4 ∧ p4)) ∧ (((p3 ∨ p1) → p2) ∨ p3)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855304885409278478651798896120 : (((((p2 → ((False ∧ ((False ∧ p5) ∨ (p4 ∨ (((p5 → p3) ∧ False) ∧ ((((False ∧ p3) → p2) ∨ p5) → True))))) ∨ p2)) ∧ True) → p1) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → ((False ∧ ((False ∧ p5) ∨ (p4 ∨ (((p5 → p3) ∧ False) ∧ ((((False ∧ p3) → p2) ∨ p5) → True))))) ∨ p2)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



