variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174326720774964544464336709295 : (((p5 ∨ ((False ∧ (True → (p2 → p4))) ∧ (p3 ∧ True))) ∨ ((True ∨ True) ∧ p1)) → (((p2 → (p3 ∧ (p1 ∧ (p5 → p3)))) ∧ False) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59962295174233380836361908136 : (((True ∨ p4) → (p1 → ((((p2 → p3) → (p2 → ((p1 → ((((True ∨ p3) ∧ p5) → (p1 ∧ p2)) ∨ p2)) → p4))) ∨ p1) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134415206279516114523719476796 : (((p2 → ((p3 ∨ True) → (p4 ∨ ((p4 ∨ ((p4 → p5) ∨ p2)) → (p4 ∨ ((p2 → (p2 ∨ p2)) ∨ p4)))))) ∨ False) ∨ (p1 ∨ (p1 → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191741149495753862952276254968 : ((False ∨ (((p4 → p3) → False) ∧ ((True ∨ p5) → p5))) ∨ (((p2 ∧ p4) ∨ p1) ∨ ((p3 → ((p3 → True) → (p2 ∨ (p4 ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198130589284079736297966738674 : (((p1 ∧ True) → (True ∧ (p2 ∨ (p5 ∧ True)))) ∨ ((p3 ∧ (((p4 → p4) → (p1 ∧ (False → p2))) ∧ ((True → (p5 ∨ p5)) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328019674895449393275758526196 : (True → ((p3 → ((p3 → (p1 ∧ ((p5 → p3) → ((True ∨ (p3 → ((p1 ∧ False) ∧ p1))) ∨ (p1 → p4))))) ∨ (p2 ∧ p4))) → (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54582648655813229723563307881 : (((p3 ∨ (((p2 ∧ (False ∧ True)) ∧ p2) ∨ p3)) ∨ (((p5 ∧ ((True → (p2 ∧ False)) ∧ ((False → p3) ∧ p2))) ∧ (p2 → p5)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166173004128409722215044000790 : ((False ∧ (False ∨ (p2 ∧ (((p1 → (p1 → p2)) → (p3 ∧ (False ∨ (p5 ∧ p3)))) → p2)))) ∨ ((p5 → (p1 ∨ (p5 ∨ p3))) ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157145919689854111863660406775 : (((((((p3 → (((p4 → p1) ∧ p3) ∧ False)) ∨ p4) ∧ ((p3 → p2) → p5)) → p1) ∨ True) → False) ∨ ((p2 → p1) → ((p5 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327184237430638002865153357087 : (True → ((p2 ∨ (((False ∨ ((p2 → (p5 ∨ ((p1 ∧ (p1 → ((p3 ∧ p3) ∧ (p2 ∨ False)))) ∨ False))) ∨ p2)) ∧ True) ∧ (p3 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342893368904581512686220305733 : (p2 → (((p1 ∨ (p1 ∨ (False ∧ True))) → p3) → ((p1 ∧ (p4 ∧ (((p4 ∨ ((p4 → p4) ∧ (p5 → p3))) ∨ True) ∨ (True ∨ False)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674828746184433092314409685877 : ((((p5 → (((p1 ∧ p4) ∧ ((((True ∨ p4) ∨ ((p1 ∧ p1) ∨ True)) ∨ p4) ∧ p1)) ∨ ((True ∨ p3) ∨ p4))) → ((p4 → False) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134185050649751604204217512231 : (((((True → (p5 ∧ (p1 → (True ∧ p5)))) ∨ ((p1 ∧ p3) ∨ p1)) ∨ ((True ∧ p3) ∨ (p2 → (p5 ∨ p1)))) ∨ False) ∨ (True ∨ (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110888287052130936092249308629 : (((((((p1 ∧ (True ∨ p4)) ∨ (p3 → False)) ∨ (True ∨ True)) → ((p5 → p1) → (((p2 ∧ p1) → False) ∧ p1))) → p3) ∧ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44128611343824106509390755733 : (((((p5 ∨ p4) ∨ ((((p1 ∨ p2) → p4) ∧ (p2 ∧ (p2 ∧ (p2 → ((p1 ∧ p4) ∧ True))))) ∧ True)) ∨ ((p5 ∨ False) → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708359444309373869899854104417 : ((((((p3 ∧ (True ∨ p5)) ∧ (p4 → p1)) ∧ p3) → ((p1 ∨ ((((p5 ∨ p5) ∨ True) → ((p1 ∧ p4) ∨ p4)) ∨ p5)) ∧ (True ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229831428552086335958102871666 : ((p5 → (p2 ∧ p1)) ∨ (p4 → (p3 ∨ ((((((p1 ∧ (p4 → p1)) ∨ (p1 → p1)) → False) → False) → ((p5 ∨ (p5 ∧ p3)) → p1)) ∨ p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209406754075823946951372027617 : ((p1 → (p3 → ((p4 ∨ False) → p1))) → ((((p4 ∨ True) ∧ p4) ∨ True) ∧ (((p5 → False) ∧ (p2 ∧ p4)) ∨ (p1 → (p3 ∨ (p1 ∧ p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94424986249801254173042096700 : ((p2 ∧ (True ∧ (((p2 → ((True → p1) ∨ (p4 ∧ (p3 → p1)))) ∨ (((p5 ∨ (p5 → False)) ∧ ((p4 ∧ True) ∨ p5)) ∨ True)) → False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → ((True → p1) ∨ (p4 ∧ (p3 → p1)))) ∨ (((p5 ∨ (p5 → False)) ∧ ((p4 ∧ True) ∨ p5)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57044238234466588712216183959 : (((p3 → (p4 ∧ p2)) ∧ ((p2 ∧ p3) ∨ (((False ∧ p1) ∧ p5) ∨ (p5 ∨ (((((p5 ∧ (p2 ∧ p2)) ∧ p4) ∨ p1) → p2) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351004437520721480527740197027 : (p4 → ((p2 ∨ (((False ∧ (True → (((False ∨ True) ∨ p1) → p1))) → (p1 ∨ p4)) → ((p2 → p1) → (p3 ∧ (p1 → p5))))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53162512768512111533418438481 : ((((p1 ∨ ((p1 ∧ (p3 → (p5 → True))) ∨ (False ∨ p2))) ∨ p1) ∨ ((p4 → True) ∧ (p1 ∨ ((((p3 ∧ p3) ∧ p5) ∧ False) → p1)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241833873957508024420664281359 : ((p1 → p1) ∧ (((((p2 ∧ p1) → (p5 ∨ p4)) → False) ∧ ((((p1 → p4) ∨ p4) ∧ (p2 → (p5 ∧ (p1 → True)))) ∧ p1)) → (p4 ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h22 : ((p2 ∧ p1) → (p5 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h26 := h13 h22
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h28 : ((p2 ∧ p1) → (p5 ∨ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h32 := h13 h28
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_491449054779454528441591288963 : ((((((p2 ∧ False) ∧ p1) ∨ False) ∨ (False ∨ ((True ∨ (((((False ∧ (True → True)) ∧ p5) → (p3 → True)) ∧ p1) ∨ p2)) ∨ (p5 → p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353684575482232658201030504032 : (p4 → (p5 ∨ ((False ∧ (p1 → True)) ∨ (p1 ∨ ((((p3 → (((p5 → (p4 ∨ p1)) ∧ p2) ∧ (True ∨ p5))) → (p1 ∧ p2)) ∧ False) ∨ True))))) := by
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
theorem thm_5_vars_165492222676582070557509530847 : ((((p4 ∨ p4) ∧ (((p2 ∨ p1) ∨ (p1 ∧ p2)) ∧ p3)) ∨ (p1 ∧ (p5 ∧ (True → p5)))) ∨ (((p3 → p3) ∨ p4) ∨ (p4 ∧ (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186150955673839264117569727974 : ((((p4 ∨ p1) ∧ (p4 ∧ ((p3 ∨ (p4 → True)) ∨ False))) ∨ p1) → (((p4 ∨ (((False ∨ (p4 → p3)) ∨ (False ∧ True)) ∧ p4)) ∧ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h4.left
      let h14 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257668729915515134471743258551 : ((p3 ∨ p3) → ((p1 → ((True ∧ ((p5 ∧ ((p3 ∨ (p5 → (((p2 ∧ p3) ∧ p2) ∧ False))) ∧ ((p5 → p3) ∨ True))) → False)) ∨ True)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343239559902559786042491698965 : (p2 → ((p1 ∨ (p5 → p4)) → ((((((True → True) ∧ p5) ∨ (p2 → (p5 → ((p3 ∧ p4) ∧ False)))) ∧ p4) ∨ ((p5 ∨ True) ∨ p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186697140256747238322250667327 : (((((p1 ∧ (p1 ∨ p3)) ∨ False) ∨ p4) ∨ (p1 ∨ (p1 ∨ p4))) → ((p2 ∧ (True ∧ (p5 ∧ True))) → ((True → p5) ∧ ((True ∧ p3) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h8
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h8
  -- Conjunctions on the left can always be decomposed.
  let h24 := h2.left
  let h25 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h37 =>
        -- False on the left can always be used.
        apply False.elim h37
    case inr h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h43 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115788527933499435723456064261 : ((((p5 → (p4 ∨ False)) ∧ p3) ∧ (((((p5 ∧ p1) → True) ∧ False) ∨ p2) ∧ (((p2 ∨ (True → p5)) → False) → (p1 ∨ p3)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137110141673146056127750508639 : ((True ∧ ((p1 ∨ (p2 ∨ ((((p4 ∨ (p2 → p4)) ∨ (p1 ∨ True)) ∧ p3) ∧ True))) → (p5 ∨ (p2 → (p5 → p1))))) ∨ ((False ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730344195853456901601912219066 : (((((p5 → p5) → p5) → (((((False ∨ ((p3 → False) → p1)) ∧ (p5 ∧ (p3 ∨ (p2 → False)))) ∧ (p2 → p3)) → (p3 ∧ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804462940681109939427793186809 : (((p3 → (((((p3 ∧ (p1 ∨ True)) ∧ p1) ∨ False) ∨ p5) ∨ (((p4 ∨ (p4 → (((p2 → True) → p3) ∨ (p5 → p1)))) ∨ p5) ∧ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42627648373419574144281559531 : (((p3 ∨ ((p5 ∧ (p4 ∨ p3)) ∧ ((p5 ∨ (True ∨ (True → p3))) ∧ (p5 ∧ ((p4 ∧ (((p1 ∨ True) ∧ p2) → True)) ∧ p5))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2470172372896552358746989682 : ((p5 ∧ ((p2 ∧ (False → ((p1 → p2) → False))) ∧ p5)) ∨ (((p2 ∨ (True → False)) → (False ∨ (True ∨ (p4 ∧ (p1 ∧ False))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197546916931999285405123446959 : ((((p1 → (True → p4)) ∨ p2) ∨ (False ∧ p5)) ∨ ((p2 ∨ (((p4 ∧ (p5 ∨ (p5 ∨ p2))) ∧ ((p3 ∧ p2) → p2)) ∨ (p1 → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192487213201793537919985899575 : (((((False → p1) ∨ False) ∨ (False → (True ∧ True))) ∨ p4) → (((((((p1 ∧ p4) → True) ∧ (False ∨ p4)) ∨ p1) ∨ p1) ∧ p5) → (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- False on the left can always be used.
              apply False.elim h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- False on the left can always be used.
            apply False.elim h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113299060682662077607415846052 : ((((p1 ∧ ((p4 ∧ p3) ∨ (p3 ∧ p3))) ∧ ((False → (False ∧ (p2 ∨ ((p1 ∨ p5) → p2)))) → (False ∧ p3))) ∧ (p5 ∨ p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208027977157414799614586630664 : (((True ∧ (p4 ∨ p3)) ∨ (p5 ∧ p3)) → ((p2 ∧ ((p3 ∧ (p2 ∧ (p3 ∧ p4))) ∧ p4)) ∨ (True → (True ∨ (((p1 ∨ p1) → p5) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688342099633968933542827619454 : ((((True ∧ ((p4 ∨ (((((p2 → True) ∨ p3) ∨ False) → p3) ∨ (p4 ∨ p1))) ∧ p4)) ∧ ((p2 ∧ (p2 → False)) ∨ ((True → p3) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45077031403076625443296287160 : ((((p1 ∧ True) → ((((p1 ∧ p1) ∧ p4) ∨ ((p1 ∧ p2) ∨ ((p3 ∨ p3) ∨ p2))) → (((False ∧ False) ∧ False) ∧ (False ∨ p1)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116740099453210161395974812226 : (((p4 ∧ p1) ∨ (p5 ∨ (True → (((((p1 ∨ False) ∧ (p2 ∨ (True ∨ p2))) ∧ p3) ∨ ((p4 → p2) ∨ (p4 → p1))) → p2)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260914363481804953682802307765 : ((p4 → False) → (((((True → (p5 → p4)) → p1) → p5) → p1) ∨ ((((p3 ∨ p1) ∨ ((p4 ∧ p3) → p2)) ∨ ((p4 ∧ True) ∧ p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54584153577531472730312523347 : (((p3 ∨ ((p5 → True) ∧ ((p2 ∧ p5) ∨ p4))) ∨ (True → (((p2 ∨ p5) ∧ ((p1 ∨ p1) → (p2 ∧ (p2 ∧ (p5 → True))))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329251315358470581843984838453 : (True → ((p3 → (True ∨ False)) ∧ (((p1 ∨ ((p1 → p2) → False)) ∨ (((p2 → (True → (False ∨ ((p2 ∨ p5) ∧ p2)))) ∧ p1) ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134358212623757192028625915303 : (((False ∨ (((p2 ∧ False) ∨ (p3 ∧ p2)) ∧ ((True → (False ∨ (False → ((p2 ∨ (p5 ∨ False)) → p2)))) ∧ p4))) ∨ True) ∨ (p5 → (p4 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155076898286810836325028891367 : ((((p1 ∧ p5) ∧ ((((True ∨ (True → p5)) ∧ False) ∧ p2) → p2)) → ((p1 → False) → (p2 ∧ p4))) ∧ (True ∨ (p4 ∨ ((False → p3) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134737280957151263208005228271 : ((((p3 ∨ p2) ∧ ((p5 ∧ (True ∨ (True ∨ (p1 ∧ p4)))) → (((False ∨ (p3 ∨ p5)) ∧ (True → p2)) ∧ p3))) → p2) ∨ ((p5 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158967538822655116456071164282 : ((p3 ∨ ((p1 ∧ (((False ∨ (True → ((((True → p4) ∨ True) ∧ p3) ∧ p5))) → p1) ∨ p2)) ∧ p2)) ∨ ((((True → False) → p3) ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_178778665820428788017559201515 : (((p2 ∨ (False ∨ True)) ∧ ((((p1 → p2) → (p5 ∧ p1)) ∧ p3) ∧ p5)) ∨ (p1 ∨ (False ∨ (True ∨ (p1 ∧ (p5 → (p1 ∨ (p4 ∨ p3)))))))) := by
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
theorem thm_5_vars_264852328311463121331201748705 : (True ∧ ((p4 ∨ p1) ∨ ((False ∨ (False ∨ (((p4 ∨ (((p4 ∨ (False ∨ (p5 → p4))) ∨ p1) ∨ p3)) → (p3 ∧ p2)) ∨ (True ∧ True)))) ∧ True))) := by
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
theorem thm_5_vars_155567585468862024142169141894 : (((p1 ∨ (p4 → True)) → ((p4 ∧ False) ∨ ((((p3 ∨ p2) ∧ p1) ∨ ((True ∧ False) → True)) ∨ True))) ∧ ((((p3 ∧ False) ∧ False) → False) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213214584771993678586658265882 : ((((p3 → p5) ∨ p5) ∧ p5) ∨ ((p2 → (p2 → p2)) → ((((p2 ∨ p4) ∨ True) ∧ (((p3 ∨ (p2 ∧ p4)) ∨ p3) ∧ (True → False))) → p1))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h11 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h12 := h8 h11
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h17 := h8 h16
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h20 := h8 h19
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h26 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h27 := h23 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h31 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h32 := h23 h31
          -- False on the left can always be used.
          apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h35 := h23 h34
        -- False on the left can always be used.
        apply False.elim h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h4.left
    let h38 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h42 := h38 h41
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h46 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h47 := h38 h46
        -- False on the left can always be used.
        apply False.elim h47
    case inr h48 =>
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h49 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h50 := h38 h49
      -- False on the left can always be used.
      apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223595059502949964990645625574 : ((p1 ∨ (True ∨ p1)) ∧ ((((p5 ∧ p4) ∧ p3) ∧ p4) ∨ (((p2 ∧ (((p2 ∨ p5) ∨ p4) → (True ∨ (p2 ∨ True)))) ∨ p4) → (p5 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252268809286723849019900194138 : ((p4 → p5) ∨ ((False ∨ ((((p5 → ((p4 ∨ p2) → ((p4 ∨ (p2 ∧ True)) ∧ p4))) ∨ p5) ∨ (p1 → ((False ∨ False) ∨ p1))) ∨ p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9388479292556475755617427671 : (((((True → (p1 → p1)) ∧ p1) ∨ (p2 ∨ (p1 → ((((p3 → ((p4 ∧ False) → False)) ∨ p5) → (p1 → (p3 ∨ False))) ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299388967808617857060576124894 : (False ∨ ((True ∧ ((((False → False) ∧ (False ∨ p5)) → ((p2 ∧ (p2 ∨ p2)) ∨ ((p4 ∨ (((p5 → p4) ∧ False) ∨ p1)) ∧ p4))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170657710319342704958280261824 : (((p4 → p2) → ((False → ((p1 ∧ False) → p5)) ∨ (p4 ∧ ((p1 ∧ p1) → False)))) ∧ ((((p4 ∧ p1) ∨ p3) ∧ (False ∧ (p2 → p1))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197398757854040132429598816299 : (((True → (((False → p2) ∧ p2) ∧ p1)) → p3) ∨ ((p1 ∨ p2) → (p3 ∨ ((p1 → True) ∨ (((True ∨ True) ∨ ((p3 ∨ False) → False)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147141845441320994090968043898 : (((False ∧ ((p2 ∧ p4) ∨ (((((p1 ∨ ((p3 ∨ p4) ∨ p4)) → p1) ∧ p2) ∨ p2) ∧ (p1 ∨ False)))) ∧ p1) ∨ (False → ((False ∧ p1) → p1))) := by
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
theorem thm_5_vars_192010798197896659490176270056 : ((p1 → (p5 ∧ (p4 ∨ (((p5 → p1) ∧ True) ∧ False)))) ∨ (((p1 ∨ (p3 ∧ p5)) ∨ (((p4 ∨ p4) ∧ ((p2 ∨ p5) ∧ p3)) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_59901450097676455285995525087 : (((p5 ∧ p1) → ((((True ∨ ((p2 → True) ∧ (((p1 ∨ (p4 → (p2 ∧ p3))) ∨ False) ∧ p4))) ∧ (p2 → (p5 ∧ p3))) → p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_46561187799325619680597329734 : ((((True → True) → (p5 ∧ (((p3 ∧ (p3 → p1)) ∨ p4) → (((True ∨ (p1 → False)) ∨ p5) → ((p3 ∧ p1) ∧ p5))))) ∧ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352043772314912385242999495555 : (p4 → ((p3 ∧ (((p2 ∧ False) ∨ p3) ∨ (p4 ∨ p4))) → (False ∨ (((((p5 → (p3 → (p3 ∧ True))) → p3) ∧ (p5 → p3)) → False) → p5)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (((p5 → (p3 → (p3 ∧ True))) → p3) ∧ (p5 → p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h9
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h11
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : (((p5 → (p3 → (p3 ∧ True))) → p3) ∧ (p5 → p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h21 := h17 h18
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : (((p5 → (p3 → (p3 ∧ True))) → p3) ∧ (p5 → p3)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h3
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h24
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616212302184740667525855603371 : (((((p1 ∨ (p3 ∨ ((p2 ∨ (((p5 ∨ p5) ∨ True) → p1)) ∧ p1))) ∧ ((((p5 ∧ p4) ∧ (p1 ∧ p3)) ∨ p3) ∧ (True ∧ p2))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_57004518356456791620958362933 : (((True → (p5 ∨ p4)) ∧ (p5 ∨ (((((True → (((((False → p1) ∨ p3) ∧ p3) ∧ p2) ∧ p3)) ∧ p1) ∧ p5) ∧ (True ∨ p3)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160479062406647417494950118704 : (((p4 ∨ (((p2 ∨ p3) ∧ p5) → (True → (((False ∧ False) ∧ p4) ∧ p2)))) → (p4 ∨ (p3 → p4))) → ((p2 → p1) ∨ (False → (p4 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136965609770060220715574427484 : (((p1 ∧ p2) → ((p1 ∧ (((p2 ∧ p1) ∨ p4) → ((p3 → p3) → p4))) → (((p3 → p5) → (True ∧ p3)) ∨ p1))) ∨ ((False ∨ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53150790938470337506870489447 : ((((((p4 ∨ (True ∧ p4)) ∨ ((p3 → p3) ∧ True)) → p4) ∨ False) ∨ ((p2 → ((p5 → (p2 ∨ ((p5 ∧ False) ∧ p3))) → p4)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314003124398762147588918935497 : (p3 ∨ (((p2 → p5) → ((p1 ∨ ((p1 ∧ p1) → False)) ∧ ((p5 → ((p1 ∨ True) → ((False → (True ∧ p3)) → p4))) ∨ True))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322236053310313870421751368629 : (p5 ∨ (((((p4 → (p5 ∨ (((((p2 ∧ True) → (p5 ∨ False)) ∧ (p5 ∧ p4)) ∧ (p1 → p2)) ∨ (p5 ∨ p2)))) ∧ p5) ∧ p4) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102965304143617542532026213771 : (((((True → ((p3 ∧ p1) ∧ ((p5 ∨ p4) ∨ (True → (False ∧ p5))))) ∨ p5) ∨ (p5 ∨ ((p4 ∨ (p5 ∧ True)) → True))) ∨ p1) ∧ (p5 → True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207400848195936102861872672811 : (((p3 ∧ (p4 ∧ (False ∨ p1))) ∨ p3) → (p4 → (p5 → (False ∨ ((p1 → False) → ((((p1 → p3) → p1) → (False ∨ p2)) ∧ (p2 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- False on the left can always be used.
      apply False.elim h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h17
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : (p1 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h18
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h21 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h21
    -- False on the left can always be used.
    apply False.elim h22
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148052193382809758185713443892 : (((False ∨ ((((p1 ∧ False) ∧ (p4 → (p2 ∨ p3))) ∧ (((p5 ∧ p2) → p5) ∨ p5)) ∧ p1)) ∨ (p5 ∨ p1)) ∨ ((p3 ∧ p3) → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431121898837639679550945490545 : (((((p2 ∨ p2) → (((p2 ∧ ((((p5 ∧ p2) ∨ ((p1 ∨ p3) ∧ ((p5 ∨ p1) → False))) → p5) ∧ True)) ∨ p2) ∧ p2)) ∨ (False ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62324887790178251914907606249 : ((p3 ∧ (((p2 → (((False ∨ False) ∨ (p1 → p2)) ∧ ((p1 ∧ p3) ∧ ((p4 → p5) → p2)))) ∨ ((p4 ∨ p5) ∨ p2)) → (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213169976825720308576815205433 : ((((p5 ∧ p4) ∨ p5) ∧ p5) ∨ (False ∨ ((p4 ∧ p5) → (p3 ∨ (p1 → ((p1 ∧ (True ∧ (False ∧ (False → ((False → False) → p2))))) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113144049964920698976906042239 : (((p3 → ((((((False → (p4 ∧ True)) → (True ∧ p4)) ∨ (p5 ∧ p3)) ∧ p4) ∧ (p2 → (p3 → (p5 ∧ p1)))) ∨ p3)) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205200859243139317853432315532 : (((p1 → (p4 → p3)) ∧ (False → False)) ∨ (((p1 ∨ ((p4 ∧ p2) ∧ ((p4 → ((p2 ∧ p5) ∨ p1)) ∧ p3))) ∧ p2) ∨ ((p5 ∧ p3) → p3))) := by
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
theorem thm_5_vars_198830082872978457678247248261 : ((p1 → (((True ∨ p4) ∨ p4) → (p4 ∧ False))) ∨ (True → ((p3 → ((p5 ∧ True) ∨ (p1 → (p1 ∨ ((p1 → (True → True)) ∨ True))))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786402321800837053043808360193 : (((p4 ∨ (((True → (False ∧ (True → p4))) ∨ ((p2 ∨ False) ∧ (p5 ∨ (True → p1)))) ∧ (((p5 → (False ∧ (p5 → True))) ∨ p3) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1627464887209287561218340606 : ((((p2 ∨ p2) ∨ (((True ∨ (((p1 → p3) ∨ p4) → p3)) ∧ p2) ∧ p1)) → ((p4 → (p4 → p5)) ∨ (p3 ∨ p3))) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193506360956400101629645009226 : (((p5 ∨ p3) ∨ ((False → p5) → (p2 ∨ (p2 ∧ p5)))) → (p1 ∨ ((p3 ∧ ((True ∨ ((p1 ∨ (p1 ∨ p1)) → p3)) ∨ p3)) ∨ (True ∨ p2)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208782430956972425900188181533 : ((p2 ∧ ((p2 → False) → (p5 → p1))) → ((((True → (p3 → (False → (p5 → p3)))) → p2) ∧ ((p3 → (p5 ∨ p1)) ∨ (p2 → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36040961197436819292816297115 : ((p3 → (((p3 ∨ False) → p5) → (((False ∨ (p4 ∧ (p3 → p2))) ∨ ((p5 → p4) → p2)) ∨ (((False ∧ p1) → (p4 ∨ p2)) ∧ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151537610131344860374287095487 : (((p3 → ((p4 ∧ False) → ((((((p4 → p5) ∧ p5) ∨ p1) ∧ False) ∧ False) → (p1 ∧ False)))) ∨ (p3 → p2)) → (((True ∨ True) → p3) ∨ True)) := by
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
theorem thm_5_vars_123249687879020073515914320663 : ((((p4 ∨ False) ∧ (p5 ∧ ((p5 ∧ ((False → p3) → ((p5 → p2) → (p5 ∧ p1)))) → p2))) ∧ (p3 ∧ (p1 → (p1 → p4)))) → (p3 ∨ True)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326916777217221012996275805494 : (True → (((((((True ∧ ((p2 ∨ p5) ∨ (True ∧ False))) ∨ p2) → p5) → True) ∨ (p1 ∧ (p4 ∧ (False → (p2 ∨ (p4 ∧ p4)))))) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244278252586644777245368876896 : ((False ∧ True) ∨ ((((p5 → p5) → p3) → False) → (((((p3 ∧ True) → p2) ∨ (p1 ∧ p5)) → p2) ∨ ((((p1 ∨ p3) → True) ∨ False) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137200255569527338307512843829 : ((False ∧ (p5 ∧ (((((p2 ∧ p5) → p2) ∨ p5) ∨ p4) → (((((p2 → p2) ∧ False) → p5) → False) ∨ (False ∧ p3))))) ∨ ((p4 ∧ False) → False)) := by
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
theorem thm_5_vars_179827714228769348904409981527 : (((p3 ∧ (((False → p1) ∨ p3) ∨ (((p2 ∧ p5) → True) ∧ p1))) ∧ p2) → (((False ∨ (p5 ∨ ((False → p3) ∧ (p5 ∨ p4)))) → p1) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56714266198930007833716578258 : ((((p5 ∧ p5) ∨ p4) ∧ (((False ∧ (p4 ∨ p3)) ∨ p4) ∨ (p2 ∧ ((False ∨ (p2 ∧ True)) ∨ ((p2 ∨ p5) ∧ ((p5 → p4) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341749145682350243035745303487 : (p2 → ((p3 ∧ (((p3 → p4) ∨ p2) → (((p2 ∨ (((((p5 → (p1 → p2)) ∧ p3) ∨ p2) → p5) ∨ p2)) ∧ p1) ∨ p3))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113125208534189482477370313303 : (((p1 → (((((p2 ∨ (((p1 → p3) ∨ False) ∨ (p2 ∨ p5))) ∨ p3) ∨ False) → False) ∨ ((p4 → (p1 → True)) ∨ p1))) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_523256690351135756555407003325 : (((True ∧ (((p1 ∨ p1) ∨ (((((p4 ∨ p3) → ((p1 ∨ (True → (((p5 ∧ p4) ∧ False) ∧ p3))) ∧ p3)) ∨ p3) → p3) ∨ True)) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244980045488859579716908837899 : ((p1 ∧ p4) ∨ ((((p4 ∨ p4) ∨ p2) ∨ (True ∨ (((p3 → True) → ((p5 → (False → False)) ∧ ((p5 → p5) ∧ False))) → (p3 ∧ p4)))) ∨ p4)) := by
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
theorem thm_5_vars_174729021528869876792926516172 : ((((p3 ∨ p4) ∨ True) → ((p3 ∨ (p5 ∨ (p5 ∨ False))) ∨ (p1 → (p1 ∨ p1)))) → (p5 → (((True → ((p4 → p3) ∨ True)) ∨ p2) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14013785645149256717561883555 : ((((p2 ∧ (True → ((p1 → (p4 → ((p5 ∨ p2) ∨ p4))) ∧ False))) → (p4 ∧ (((True → (p3 → p4)) → False) ∧ p5))) ∧ (p2 → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113682500181239404534386766233 : ((((((p4 ∧ ((((p5 ∧ p1) → p5) → (((p3 ∧ False) ∧ True) ∧ p1)) ∨ (p5 ∧ p1))) ∨ False) ∧ p1) → p1) → (True ∧ p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



