variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250085796711189911641594822449 : ((True → p4) ∨ ((((p3 → ((p2 → (p1 ∨ ((p2 ∧ p3) ∨ (True → True)))) ∧ (True ∨ p3))) → p2) ∧ ((True ∧ (p5 → p5)) ∧ True)) → p2)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → ((p2 → (p1 ∨ ((p2 ∧ p3) ∨ (True → True)))) ∧ (True ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711849615126969045008995573532 : (((((False ∧ ((p1 ∧ p3) → False)) ∧ p5) ∨ (p3 ∨ ((False ∧ p2) ∨ ((((p1 ∧ (True ∧ p3)) → p2) → (p3 → True)) ∨ (p5 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611985573897416762200422394227 : (((((((p2 → p1) ∧ (p3 ∨ (p2 → ((p4 → ((True ∨ (p1 → (p4 ∨ (p1 → p1)))) → p1)) → False)))) ∨ True) ∧ (p4 → True)) ∨ p1) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118710058251026020143891232030 : ((p5 ∨ ((p3 ∨ (((((p5 ∨ ((p5 ∨ p2) ∨ False)) ∨ p2) → (False ∧ (p4 ∨ (p2 → False)))) ∨ p2) → (p4 → False))) → p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322387477844066543685509061409 : (p5 ∨ (((((((p5 → p1) ∨ p4) → ((p5 → (p3 ∧ p3)) ∧ (False ∧ False))) ∧ p5) → p1) → ((((p2 ∨ False) → False) ∨ True) ∨ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172500267527870809012996830761 : ((((p2 ∧ p3) ∧ p4) ∧ (p5 ∧ (((p2 ∨ (p5 ∨ (p5 ∨ p2))) → p5) → True))) ∨ (p5 → ((p5 → (((p5 ∧ p3) ∨ p1) ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753423114017795844724895877272 : (((False ∧ ((((p1 ∨ p5) → (((False → p1) ∧ p4) → p4)) → (((p3 → True) ∧ p4) → (p5 → (p2 → p1)))) ∨ ((True ∧ False) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727884025342251544988143389621 : ((((p2 ∨ (p1 ∧ False)) ∨ (((False → ((((False ∨ p3) ∧ False) ∨ p3) ∧ p3)) ∧ ((p5 → p3) → p3)) ∨ ((p1 → (p1 → p1)) ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114739211880908047298372898969 : ((((True ∨ (True → p5)) ∨ ((((False ∧ p4) ∧ ((p1 → p4) → p3)) → True) ∧ p2)) → (((False ∨ p4) → (p1 ∨ True)) → p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682910459183408294388011574350 : (((((p1 → p5) ∧ (p2 ∧ (p2 ∧ (((p1 ∨ p5) ∨ (((p1 → p3) ∧ p4) ∧ p2)) ∧ True)))) ∧ (((p2 ∧ (p5 ∧ p5)) ∧ True) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347002707385430372353768304219 : (p3 → ((((((p5 ∧ (((p2 ∧ p5) ∨ p3) ∧ p5)) → (p4 ∨ p4)) ∧ p5) ∨ False) ∨ p2) ∨ (p1 → (p1 → (((False ∨ False) ∨ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321061397157236966928346996553 : (p4 ∨ (p1 ∨ ((((((p2 ∧ p1) ∨ (p3 ∨ True)) ∨ p1) ∨ ((((p2 → (p3 ∨ False)) ∧ p1) ∧ p5) ∧ False)) ∧ (True ∧ False)) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_118222604390262950886467299382 : ((p1 ∨ (((p4 ∨ (p2 → ((p2 ∨ True) → ((p5 → p5) ∨ True)))) → (((((p4 ∧ p4) → p5) ∨ False) ∧ p4) ∨ p1)) ∨ True)) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147976725566460949300222994004 : (((((((p1 ∧ (p1 ∨ (p4 ∨ p2))) → p3) ∧ (p5 ∧ ((p4 ∧ p5) ∨ p3))) ∨ p5) ∧ False) ∨ (p2 ∨ p5)) ∨ (p4 ∨ (False → (p1 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350806557579512274335554496903 : (p4 → (((p3 → (p1 ∧ (((True → False) ∧ ((((p1 → p3) ∧ False) ∧ (p4 → ((p3 ∧ True) ∧ p3))) ∨ p2)) ∨ False))) ∨ p4) ∧ (True → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178761201639324765053316961111 : ((((p3 → False) ∨ p4) ∧ (p4 ∨ (((p5 → p3) → True) ∨ (p1 → p3)))) ∨ ((p3 ∧ ((p4 → ((p2 ∨ p5) → (True ∧ p2))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65836412109713955312571033072 : ((p4 ∨ ((p4 → ((False ∧ p2) → p4)) → (p5 ∧ (p4 ∧ ((((p5 → ((p5 ∧ p2) ∧ p3)) ∨ True) ∧ False) ∧ ((p1 ∧ p5) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_839716493737872673017646799164 : (((((((((p2 → p3) ∧ (((p4 ∧ p4) ∨ (p3 ∧ False)) ∨ (p2 ∧ False))) → p2) ∨ p3) ∨ (p2 → (p1 → True))) → (p3 ∧ False)) ∨ p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((((p2 → p3) ∧ (((p4 ∧ p4) ∨ (p3 ∧ False)) ∨ (p2 ∧ False))) → p2) ∨ p3) ∨ (p2 → (p1 → True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h3
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217008846367957983589065909478 : ((((False ∧ p4) ∧ p3) ∨ True) → ((p1 → ((((((p3 ∧ p3) ∨ True) ∨ p3) ∧ ((p5 ∨ p2) ∧ p3)) ∨ p5) ∧ (True ∧ (p5 ∧ p2)))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56940774464191182145352567376 : (((False ∨ (p3 → p1)) ∧ ((p5 → p2) ∨ ((p1 ∨ ((p2 ∧ p5) ∧ ((False ∨ p5) ∧ False))) ∧ (p1 ∨ (((p2 ∧ p4) ∨ False) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699191411485101337067355952750 : ((((p2 → (((False → (p3 → p5)) → False) ∧ ((p3 ∧ p1) ∧ p4))) ∨ (((True ∨ p4) ∨ False) → (p5 → ((p5 ∨ p1) ∨ (p1 ∧ p4))))) ∨ p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40244893571905176253432798401 : ((((p5 ∧ (p2 ∧ (((True → ((p4 ∧ False) ∨ (p3 ∧ p5))) ∨ (True ∨ (((True → (p5 ∨ p3)) ∨ p3) ∧ p1))) ∨ p4))) ∧ p3) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232976113129369591309942842086 : ((p3 ∧ (p1 → p3)) → ((p1 ∨ p2) ∨ (p3 → (p4 ∨ (((p3 ∧ p1) ∧ ((p5 ∧ True) ∧ True)) → (p4 → ((p5 → (True → p2)) ∨ p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h8.left
  let h12 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225412218683723080162428881542 : (((p3 ∨ False) ∧ p2) ∨ ((p5 ∨ p1) ∨ ((False ∨ (True ∧ (p5 → p5))) ∨ (((p2 ∨ p3) → (p3 ∧ (p5 → (p4 ∧ (True → p3))))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_178544019837785388127008080840 : (((True → ((p5 ∧ (p3 → True)) ∧ (True → p4))) → (False ∨ (p2 ∧ p3))) ∨ (p3 → (((True ∧ False) ∨ ((p5 → p2) ∨ True)) ∧ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340397996285992829311630999142 : (p2 → ((((((p1 → (p4 → p5)) → p1) ∨ ((p2 ∨ p5) ∨ p2)) → ((p2 ∨ p2) → (p2 ∧ (p1 ∨ (True ∨ False))))) ∨ (True ∧ False)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336354010100553857912339519871 : (p1 → (((p5 ∧ p4) ∨ ((((((True → p4) ∨ p4) ∨ ((True ∧ ((p5 ∨ p5) → (p1 ∧ (p4 → p4)))) ∧ False)) → p1) ∧ p1) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47069804429672293220562478118 : ((((p3 ∧ ((((p3 ∨ p3) ∨ (True → ((((p4 → p5) ∨ p1) ∨ p5) ∧ p1))) ∨ (False ∨ p2)) ∧ p1)) ∨ (False → p2)) ∨ (False ∨ p4)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320055554094279857263504489466 : (p4 ∨ ((False ∨ (p5 ∧ p2)) ∨ (((p5 ∨ ((p4 → (True ∧ p4)) → p5)) ∨ (p4 ∧ p5)) ∨ ((False ∧ (((False ∧ True) → p5) → p4)) → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245597226670278685112328215817 : ((p3 ∧ False) ∨ (((p4 ∧ ((p3 ∨ (False → ((False ∧ p1) ∧ (((True ∨ p2) ∧ (False ∨ p2)) → True)))) → p2)) ∨ (p3 ∨ True)) ∨ (p4 ∨ p4))) := by
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
theorem thm_5_vars_55292415447661379754268751694 : (((p2 ∧ (p5 ∨ ((p1 ∧ p1) ∧ p5))) ∨ (p5 → (p1 → (p1 ∧ ((p3 ∧ (p2 ∨ (p2 → (False ∨ (False ∧ p5))))) → (False ∨ p1)))))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184488875560595667655030506124 : ((((p3 ∧ (False ∨ (True → p3))) ∧ (p2 ∨ p2)) ∨ (True → False)) ∨ ((p3 → (((((True ∨ p2) ∧ p1) ∧ p2) ∨ (p5 → p3)) ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52229731444825988772191149013 : (((p1 ∧ (((True ∨ p2) → (((p4 ∨ (p2 ∨ p1)) → False) → (p5 ∧ p3))) → p5)) → ((((p2 ∨ p3) → True) ∨ (p1 ∨ p5)) → p5)) ∨ False) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True ∨ p2) → (((p4 ∨ (p2 ∨ p1)) → False) → (p5 ∧ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : (p4 ∨ (p2 ∨ p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h11 := h8 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h13 : (p4 ∨ (p2 ∨ p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h14 := h8 h13
        -- False on the left can always be used.
        apply False.elim h14
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h15 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h16 : (p4 ∨ (p2 ∨ p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h17 := h8 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h19 : (p4 ∨ (p2 ∨ p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h20 := h8 h19
        -- False on the left can always be used.
        apply False.elim h20
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h21 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h1.left
      let h25 := h1.right
      -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
      have h26 : ((True ∨ p2) → (((p4 ∨ (p2 ∨ p1)) → False) → (p5 ∧ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h29 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h30 : (p4 ∨ (p2 ∨ p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h31 := h28 h30
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h33 : (p4 ∨ (p2 ∨ p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h34 := h28 h33
          -- False on the left can always be used.
          apply False.elim h34
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h35 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h36 : (p4 ∨ (p2 ∨ p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h37 := h28 h36
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h39 : (p4 ∨ (p2 ∨ p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h38
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h40 := h28 h39
          -- False on the left can always be used.
          apply False.elim h40
      -- We have shown the premise of h25, we can now drive its conclusion.
      let h41 := h25 h26
      -- One of the premise coincides with the conclusion.
      exact h41
    case inr h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h1.left
      let h44 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40905820130341522162147489736 : ((((p1 ∧ ((((((p3 ∨ p2) ∨ p4) ∧ (p1 → p2)) ∨ ((p3 → (True ∧ (p3 → p1))) ∨ p4)) → False) ∨ p2)) ∧ (p1 ∧ True)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607447743935069648872950038749 : ((((((p3 → p4) ∨ (False ∧ ((True → ((True → ((p4 ∧ ((p1 ∨ p1) → True)) → p2)) ∧ (False ∨ (p2 ∨ False)))) ∧ p2))) ∧ p4) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654228994590698647331335120801 : ((((((((True → ((False ∧ (p5 ∧ p5)) → p2)) ∧ p5) ∨ ((True ∨ p1) → ((p2 ∨ (p4 ∨ p2)) ∨ True))) → p1) ∨ p3) ∨ (p3 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696963406467850648439456041458 : ((((((True ∧ False) → ((p3 ∨ False) ∧ (False → p2))) → (p3 ∨ p2)) ∧ (p3 ∧ (((True ∧ (p2 → ((p5 → p1) ∨ p5))) ∨ p5) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354721803452357437052685221192 : (p5 → ((((p3 ∨ ((p2 → (p4 → (((p1 → True) → (p3 → (p3 ∧ p1))) ∧ (False → True)))) → p2)) ∧ p4) → ((p3 ∨ False) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4521322898669653873050116008 : (p3 → (((p2 ∧ (((True → True) → ((True → True) ∨ ((p1 ∧ p2) → (True → p3)))) → (p5 ∨ False))) ∧ (p2 → p2)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41236285471010913824368140734 : ((((False ∨ ((p2 → (((False → (p5 ∨ (False ∧ p2))) ∨ p2) ∨ p5)) ∨ ((True ∨ True) ∨ True))) ∧ (p1 ∧ (False ∧ (p2 ∨ p4)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192555687510429198607116850071 : (((False ∨ (((p4 → False) ∨ (p3 → p3)) ∧ p1)) ∨ False) → (((True → (p3 ∧ (True ∧ (((p2 → (p4 ∧ p4)) → p4) ∧ False)))) → p2) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h10 := h8 h9
        -- We need to get the right conjuct of h10 based on <expert-advice>.
        let h11 := h10.right
        -- We need to get the right conjuct of h11 based on <expert-advice>.
        let h12 := h11.right
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- We need to get the right conjuct of h17 based on <expert-advice>.
        let h18 := h17.right
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307686174034660322516993912052 : (p1 ∨ (p2 → (((p4 ∨ (p3 ∧ p5)) ∨ (p2 → (((p5 → ((False ∨ p2) ∨ p5)) ∧ p4) ∧ p3))) ∨ ((((False ∨ p5) → p3) ∧ False) → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136498185680784385270980034965 : ((((False → p1) → p2) ∧ ((False ∨ ((p5 ∨ p5) ∨ False)) → ((True ∧ (p2 → (((p3 → p2) → p2) → p4))) → False))) ∨ (p3 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315438720508636226749170917476 : (p3 ∨ ((p4 ∨ (p4 ∧ p1)) ∨ ((p4 → (p3 ∨ p3)) ∨ (True ∨ (p5 ∧ ((p4 → False) ∧ ((((p3 ∧ True) → True) ∨ (p4 ∧ p3)) ∧ True))))))) := by
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
theorem thm_5_vars_59076796669863528686115620922 : (((p5 ∧ p1) ∨ ((((p1 ∧ False) ∨ p2) ∨ (((p3 ∧ False) ∧ (p1 ∨ (False ∨ p2))) → p2)) → ((p1 → (False ∨ p5)) ∨ (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198709519261933493397204512546 : ((p5 ∨ ((p5 → (p4 ∨ (False ∨ p3))) ∨ p3)) ∨ (((p2 → p4) → (p1 ∧ p4)) → ((True ∧ (p3 ∧ (True → (p1 ∨ (False ∨ p3))))) → p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9780337837732431989092688349 : ((((p5 ∨ True) → ((p2 ∨ ((p5 ∨ ((p1 → (p2 ∨ (p5 ∧ (p3 ∨ p2)))) → False)) ∧ p5)) ∨ (p5 → (p4 → (True → True))))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256356330016962394841286547232 : ((False ∨ p2) → (((p4 → p1) ∧ (p4 ∧ ((False → p5) ∧ (p4 → (p1 → (True ∨ p4)))))) → ((((p4 → False) ∨ (p1 ∨ p3)) ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136997108465630823639877855629 : (((True ∨ p2) → (p3 ∨ (p3 → ((((True ∧ (False → (p3 → (p5 ∧ p3)))) ∧ (p5 → p2)) ∧ p1) ∨ (False → p2))))) ∨ ((True ∧ p5) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68495893059634381993896160847 : ((p3 → (p2 ∨ ((((p1 → False) ∧ ((((((p5 ∨ p3) ∨ p1) ∨ p2) → p4) ∧ p3) ∨ (False → (False → p4)))) → (p2 ∧ p5)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192976763365931134890506477931 : (((p2 → (p3 ∧ (p3 ∧ (p3 ∧ False)))) ∨ (p2 → p1)) → (p4 → (p1 ∨ ((p1 ∧ ((p5 ∧ p3) ∧ p5)) → (p3 ∨ ((p5 ∧ p5) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h16
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137350354444869830770706420637 : ((p3 ∧ ((p5 ∧ ((p3 ∧ (((p3 ∨ True) → False) ∧ ((((p2 ∨ p3) ∨ (True → False)) → p2) → p1))) ∨ p5)) ∧ p2)) ∨ ((True ∧ False) → p3)) := by
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
theorem thm_5_vars_50432765251969961929206492967 : (((p5 ∧ (p1 ∨ ((p4 ∧ p5) ∧ (((False ∧ p4) ∨ p2) ∧ ((p3 ∧ True) → (p1 ∨ (p5 ∧ False))))))) ∨ ((p1 → p1) ∨ (p3 ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56254234941309109567221804522 : (((p1 → ((p3 → p3) ∧ False)) ∨ ((((p1 ∧ False) ∨ p1) ∧ p4) ∨ (p4 → (((False → False) → p4) ∧ ((True ∧ p3) → (p4 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67668069003121375847548175082 : ((p1 → (True → (((True ∧ (((True → (((p4 ∧ p5) ∨ p5) ∧ (((p5 ∨ p4) → False) ∧ (False → p5)))) ∨ False) ∧ p1)) ∨ True) ∨ True))) ∨ p4) := by
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
theorem thm_5_vars_174691382226656336905912377879 : ((((False → p1) ∨ p5) ∨ (((p4 ∧ False) ∨ (p4 → (True ∧ (p3 → p3)))) ∨ p3)) → (((True ∧ (((True ∧ True) → p3) ∨ p5)) ∨ True) ∨ p3)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150239072330114639464503358037 : ((p3 → (((p3 ∧ ((p5 → (False ∧ p1)) ∧ (p5 → True))) → (p5 ∨ ((False ∨ (p1 ∨ True)) ∧ p3))) ∨ p4)) ∨ (((p5 ∧ False) → False) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234641958356259660507582775225 : ((p3 → (p3 → p5)) → ((p2 ∨ ((p4 ∨ p3) ∨ ((False → ((True → ((p2 ∧ p1) ∧ False)) ∨ False)) ∧ p1))) ∨ ((p3 ∧ (p4 ∧ p2)) → p3))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749836994866043913430690200413 : (((True ∧ ((p2 ∨ (p5 ∧ ((False ∨ (False ∧ ((p3 ∨ ((((p2 → True) → (p2 ∧ False)) ∧ (p3 ∧ p5)) ∨ False)) ∧ p3))) ∧ p3))) ∨ True)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64404774757941030216299343477 : ((p1 ∨ (((p2 ∨ ((p4 ∨ (((p2 ∧ p5) ∧ p2) → p1)) ∨ True)) → ((p3 ∧ (p2 ∨ (p4 ∧ (p5 ∧ (p5 ∨ False))))) ∨ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43179637969436602128724040403 : (((((p1 → False) ∧ (p5 ∧ ((p2 ∧ p2) → (p4 ∧ (((p1 ∧ (False ∧ False)) → (((p5 ∨ p5) → p4) → False)) → p5))))) ∧ p1) → False) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340077810204026948121642094369 : (p1 → (p2 → (p1 → (True ∧ ((p5 ∨ ((p4 ∨ p1) ∨ (False ∨ (p4 → False)))) → (((((True → p2) ∧ (p3 ∧ p2)) → p4) ∧ False) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215947899162883448089267808234 : ((p4 ∨ ((True ∨ True) ∧ p1)) ∨ (((((p1 ∨ (p1 → p2)) ∧ ((p1 ∧ (p2 ∧ p5)) ∧ True)) → (p4 ∧ True)) ∨ (p2 → p5)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233551650974067583963982613598 : ((p1 ∨ (True → True)) → ((((False ∧ (p1 → False)) ∧ (p5 ∨ p1)) ∨ (((False ∨ (p2 ∨ (p2 ∧ ((p1 ∨ p4) ∨ False)))) → p2) → p5)) ∨ True)) := by
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
theorem thm_5_vars_116819403952182944773797020376 : (((p4 ∨ p3) ∨ ((p5 ∨ (p3 ∨ ((p4 → (((p1 → (((p3 ∨ p3) → p3) ∨ (p4 → p5))) ∧ p3) → False)) → False))) → False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40711263782498847833139507047 : (((((p3 ∨ ((((p1 → p4) → (False ∧ p5)) → False) ∨ True)) ∨ (((p3 ∧ (p1 ∨ ((p4 ∨ True) ∨ p3))) ∧ False) ∧ False)) → p4) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352047418711605376668025165212 : (p4 → ((p3 ∨ ((p5 ∨ (True ∨ p1)) → (False ∨ p2))) → ((((p1 ∧ (p5 ∨ False)) ∧ (True → (((True ∨ True) ∧ p2) → p3))) ∨ True) ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255743265462723595424403718946 : ((True ∨ True) → ((p1 ∧ ((p5 ∧ ((p2 → ((((False ∨ (p4 → p4)) ∧ False) → p3) → (p2 ∧ p4))) ∨ p3)) → p2)) ∨ ((False ∧ p1) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337047795405274173840658416611 : (p1 → ((((p3 ∨ (((((True ∧ p4) ∨ p2) ∨ p3) ∧ p2) ∨ (True ∨ (((p2 → False) → (p5 ∨ p3)) ∨ True)))) → p4) ∨ True) ∨ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218843846759019250279058661865 : ((p2 ∧ ((False ∧ p5) → p5)) → ((p5 ∨ ((((((False ∧ True) ∨ p3) ∧ (p3 ∧ (p2 ∨ ((p3 ∧ p5) ∨ p1)))) ∨ False) ∨ p4) ∧ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309915274691732196674614213094 : (p2 ∨ (((((p2 → (p2 → (p1 → ((((p1 ∧ False) → True) ∧ p3) ∨ p3)))) → p2) ∨ p4) → p4) ∨ ((False ∧ ((p2 ∨ p1) → False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252451857493934027062838507817 : ((p5 → p1) ∨ ((p4 → (((p4 ∨ p4) ∨ p5) ∧ ((((p5 → (False ∨ p4)) → p1) → p1) → (p2 ∨ (p1 → ((p4 ∧ p2) ∧ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191922623015869613639644223724 : ((True → (((p4 ∨ p5) ∧ (p1 ∧ (p5 ∨ p4))) ∧ p5)) ∨ (((p4 → True) → (p3 ∧ p1)) → (False → ((p1 → ((False ∨ p3) ∨ p5)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225135700535670509178169221902 : (((p3 ∧ False) ∧ p1) ∨ ((((p2 → True) → (False ∧ (False ∧ (p4 ∨ ((p1 ∨ p1) ∨ p3))))) → p5) → (((False ∨ p2) ∧ p4) ∨ (False → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768484597670241047478034562970 : (((p5 ∧ ((p3 → ((p2 ∧ (False ∨ (p1 ∨ (False ∨ p3)))) → (p5 ∧ (p1 ∧ (p3 → p4))))) ∧ (((p3 → False) ∨ p3) → (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60092592276208481245657173986 : (((p3 ∨ False) → ((((p1 → ((p4 → p1) ∧ ((p4 ∧ True) ∨ True))) ∧ (p1 ∨ (((p1 ∧ (p5 ∨ p3)) ∨ p4) ∧ p5))) ∨ True) ∨ True)) ∨ p2) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214705311544847589261403547989 : (((False ∧ p3) ∨ (p1 ∧ p5)) ∨ ((p3 ∨ False) ∨ (((p2 ∧ (False ∧ p4)) → (((p5 → False) → ((False ∨ p1) ∨ (p4 ∨ p4))) ∨ p3)) ∧ True))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257428773490877682537434759567 : ((p3 ∨ True) → (((True ∨ ((False ∨ p4) ∧ (p2 ∨ ((p4 → ((p3 → p4) ∧ p4)) → p1)))) → ((True → p2) ∨ (p3 ∧ (p3 ∨ p1)))) ∨ True)) := by
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
theorem thm_5_vars_598015741426171136788174553882 : (((((p1 ∨ (p5 ∨ True)) ∧ (p5 ∨ (True → (((p5 ∧ (p4 → ((True ∨ p4) ∧ (p3 ∧ p3)))) → (p3 ∧ (p4 ∧ p1))) ∧ False)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171426962220236489597428498672 : ((((False ∧ p5) ∨ (((((p1 ∨ False) → p4) ∨ (p4 ∧ p5)) ∧ p3) → p2)) ∧ p1) ∨ ((False → ((False → ((p3 ∨ p4) ∨ p2)) ∨ True)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594522087256777298736595096444 : ((((((False ∨ (((p2 → False) → False) → (p2 ∨ p5))) → (p3 ∨ ((p2 → False) ∨ p1))) ∨ (False ∧ (False ∧ (True → (p1 ∧ p3))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44284240059268234895489300044 : (((((False ∨ ((True ∨ ((p1 ∧ (p4 ∨ (True → p4))) ∨ False)) ∨ (True ∨ False))) ∨ True) ∧ (((True ∨ p5) ∧ (p4 ∨ p2)) ∨ True)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171342178706976847241473297870 : ((((((p2 ∧ ((p2 ∧ (p1 ∧ p1)) ∧ p4)) ∧ p2) → (p1 ∨ p5)) → p4) ∧ p4) ∨ (True ∧ (((p3 ∧ (False ∧ p5)) ∧ (p1 ∧ p3)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58120036694741491475306469147 : (((p2 ∧ True) ∧ (((((p2 ∧ p3) ∧ ((p5 ∨ (True ∨ p4)) ∨ True)) ∨ ((True → p5) ∨ (p4 → (p3 ∨ p3)))) → p5) ∨ (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137690867901756620613340610502 : ((p1 ∨ (((False → ((((p1 ∧ False) ∨ (False ∨ p5)) ∨ ((True ∧ p5) → p2)) → p3)) ∧ ((True ∧ p3) → p5)) → p4)) ∨ ((p5 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62067348749905800036215568487 : ((p2 ∧ (True ∧ (p4 ∨ (p4 ∨ (((p1 → (p4 ∨ False)) → ((p1 → (p3 ∨ ((p1 → p1) ∧ ((p4 ∧ False) ∨ True)))) ∧ False)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53931734184605247767270077331 : (((True → (((False → True) ∨ ((p5 → p2) ∨ p5)) ∧ p3)) ∨ ((((True ∧ (p1 → ((True ∨ p3) → (p2 ∨ p4)))) ∧ p3) → False) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206101332428782043481426969864 : ((p4 ∧ (((p1 ∧ p2) ∧ p1) ∧ p4)) ∨ ((p2 ∨ (((p1 ∧ p3) ∨ ((True ∨ p3) ∨ (p4 ∨ False))) ∧ (True → True))) ∨ ((False ∨ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87348725880103164862627846574 : ((((p3 → p4) ∧ ((p2 → p4) ∧ p2)) ∧ (p2 → ((p3 → (((p5 ∧ (p1 ∨ (p1 ∨ p3))) ∨ p4) → (p4 → p5))) → (p5 ∧ p4)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806283602746754947918052207209 : (((p4 → (((p2 → ((True ∧ p1) ∧ ((p2 ∨ False) → False))) ∨ ((((((p5 → p2) → p3) ∨ (False ∧ p5)) ∧ False) ∨ False) ∧ p3)) ∨ p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_61608848511613868845572837904 : ((p1 ∧ ((False ∨ p5) ∧ ((True ∨ (((True ∧ p1) ∨ ((p2 ∨ True) ∧ p5)) ∧ p5)) → ((p1 ∧ (True ∨ (False ∧ p2))) ∨ (p5 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263374606543220199065590597823 : (True ∧ ((((p2 ∧ (((p4 ∧ (p3 → True)) → (True → (p5 ∧ (((p4 ∨ p5) → False) ∧ p3)))) ∨ p4)) ∨ True) ∨ True) ∨ (False ∧ (p3 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108207275569638254577488612377 : (((p5 → False) → (((p4 → (((p2 ∨ (False ∨ p1)) ∧ True) ∧ True)) ∧ ((p5 ∨ p2) ∨ p3)) ∨ (p1 ∨ (True ∨ (p4 ∨ p1))))) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68253434330512269052691751911 : ((p3 → ((((((((((p5 ∧ (p4 ∧ p5)) ∨ p4) ∨ p1) ∧ True) → True) ∧ p2) ∧ (p3 ∧ True)) ∧ False) ∨ (p4 ∧ p2)) ∧ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51151523104466479030254246001 : (((((True ∨ False) ∨ (p2 → ((True ∨ ((p5 ∧ p2) ∨ (False → (p1 ∨ p2)))) → p3))) → p2) ∨ ((p2 ∧ ((p3 → p1) ∧ p4)) → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184509931860449070486452513901 : (((True ∧ ((p3 ∨ p5) ∨ (p5 ∧ (p4 ∨ p3)))) ∨ (p4 ∧ True)) ∨ ((False → (p5 → (p4 ∧ (p5 ∧ p1)))) → (p5 ∨ ((True ∧ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133914065592410180271777548259 : (((p3 ∨ (((p5 → (p2 → False)) ∨ True) ∨ ((p5 → (p5 ∧ (((p1 ∧ p4) → (p4 ∨ False)) ∨ p1))) ∨ p5))) ∧ p2) ∨ ((p2 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125183521038044222270205488554 : (((False ∧ (p1 ∧ p3)) ∨ (p3 ∧ (((p4 ∨ p5) ∧ (p4 → (p5 ∧ (p2 ∨ True)))) ∧ ((p1 ∨ ((False ∧ p2) → p3)) ∨ p5)))) → (True ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h15 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h16 := h11 h15
          -- We need to get the left conjuct of h16 based on <expert-advice>.
          let h17 := h16.left
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
          have h19 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h11, we can now drive its conclusion.
          let h20 := h11 h19
          -- We need to get the left conjuct of h20 based on <expert-advice>.
          let h21 := h20.left
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197699255963817970006446935122 : (((True → (False → (p1 → True))) → (True → p3)) ∨ ((((True → ((p3 ∨ (p2 ∨ (p4 ∧ p3))) ∧ False)) ∨ p5) ∨ ((False ∨ False) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_47645006046184373656717444977 : ((((((((p3 ∨ p4) → p1) → p1) ∨ (p3 → (p4 ∨ ((((p5 → (p2 ∧ False)) → False) ∨ p3) → p5)))) → p1) ∧ True) → (p1 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



