variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147709081320402736553327024171 : ((((True ∧ ((p2 ∨ p3) ∨ (p5 ∧ ((p5 ∧ p1) → p2)))) ∨ ((p4 ∧ (p5 ∧ (p3 → False))) → True)) → p1) ∨ (False ∨ (True ∨ (p1 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218042309984975301115895419967 : (((p2 ∨ p1) ∧ (p4 ∨ False)) → (((p5 ∨ (p4 → (p1 → False))) ∨ ((((p2 ∨ p1) ∨ (p3 ∨ ((p4 → p2) → p3))) ∨ p5) ∨ p2)) ∧ p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49279790861641955778038710316 : (((p4 ∧ ((((p3 → p2) → (((p2 → p1) ∨ (p2 ∧ (((p3 → p1) → True) ∧ p2))) → p4)) ∨ p2) ∨ p2)) ∨ ((False → False) ∧ True)) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147516973283749938019849116636 : (((p4 ∨ ((p5 → ((((False → (p3 ∨ True)) → p4) → False) → p1)) → (p4 ∧ (False ∧ (p5 ∧ p4))))) ∨ p4) ∨ (p1 → ((p5 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767115868714305156688390721238 : (((p4 ∧ (p4 → ((p1 ∧ ((((p4 ∧ (p3 → (False → p2))) → (p1 ∧ False)) ∧ (p1 ∧ p3)) ∧ True)) ∨ (p4 ∧ (False → (p1 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55242842446743675560616105438 : ((((False ∨ p1) ∧ ((True → p3) ∧ p4)) ∨ ((p1 → (((p3 → p2) ∧ (True ∧ (p5 ∨ p2))) → (((False → True) → False) ∧ p4))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260401850705005033772503344904 : ((p3 → True) → ((p4 → (p3 → (((p1 → (p3 → (False ∨ False))) ∧ ((p4 ∨ p1) ∧ (p1 ∧ ((p1 ∨ p1) → (False → True))))) → p2))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
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
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h8.left
    let h20 := h8.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h21 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h22 := h5 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135532488919804619551264556574 : ((((p3 ∧ (p5 ∧ (p2 → (((p3 ∨ (p1 ∧ p5)) ∧ p4) ∧ False)))) ∧ (p2 ∨ p4)) ∧ ((p3 → p2) → (p5 ∧ True))) ∨ ((True ∨ False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801856046687236327109633890356 : (((p2 → ((True ∨ p1) ∧ ((p1 ∨ False) ∧ (((False → p1) ∧ (p4 ∧ (((p2 → (True → False)) → (p4 ∧ (p3 ∨ p4))) ∧ True))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135428420094333986027980583316 : (((p1 ∨ ((False ∧ ((((True ∨ p1) → True) ∨ p3) ∧ ((p4 ∨ p2) ∨ (p1 ∧ False)))) ∨ p3)) ∨ (False → (p3 ∨ p1))) ∨ (p2 ∨ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52553984784099854008927319031 : (((((p2 ∧ p4) ∧ (p4 ∨ ((p5 ∨ (False ∧ p1)) ∧ (True ∧ p4)))) → p5) ∨ (p1 ∧ ((p5 ∨ p3) ∧ ((p2 → (True ∨ False)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42877579998485076203058497357 : (((p2 → (p2 → ((p5 → (p1 ∧ p4)) → ((False ∧ True) ∨ ((((False ∨ ((p4 ∨ False) → p5)) ∨ p5) → (False ∧ False)) ∨ p1))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716720434217993969790762750392 : (((((p1 → p5) → (p2 → p3)) ∧ ((((p1 → True) → (p3 ∨ p4)) ∧ (False ∨ ((p4 ∧ p4) → ((False → (True → p2)) → p4)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59407940982090601032765097612 : (((True → p4) ∨ (((p1 → True) ∧ ((((True → True) ∨ p1) ∨ True) ∧ ((p3 → p4) → ((True → (p4 → True)) → p2)))) → (p4 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614759886691705872064656465890 : ((((((((False → ((p3 → p2) → p5)) → p4) → False) ∨ (((True → True) → True) → (False ∧ p2))) ∨ (((True ∧ p4) ∧ p5) → p4)) ∨ False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147027662620298016471856748660 : (((((True → (((p3 ∧ ((p3 → (p1 → p2)) ∧ p1)) ∨ p3) → p1)) ∨ p5) ∨ ((p5 ∨ p1) ∨ False)) ∧ p1) ∨ ((p3 ∧ (True ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342411276189130173444818750557 : (p2 → (((p1 ∨ (p3 ∧ (p1 ∨ (False ∨ (p1 → (((False ∨ p4) ∨ p2) → p5)))))) ∧ p5) → ((p4 → p1) ∨ ((p1 ∨ (p4 ∧ False)) → p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- False on the left can always be used.
          apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65157715663842923767067473254 : ((p3 ∨ ((((False ∨ (((False ∨ p5) ∧ (True ∨ (p1 → p3))) → (p4 → (p3 ∧ p2)))) ∧ ((True ∧ p2) → (p2 ∧ p3))) ∧ p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207855245917853589960632920623 : ((((p2 ∧ p2) ∨ True) ∧ (p3 ∧ p3)) → ((p2 ∨ (p1 → ((((p5 ∨ (p1 → False)) ∧ (p1 ∨ p3)) ∧ (True → p5)) ∨ (p2 ∧ p3)))) ∨ p3)) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46892880785401086399441600325 : (((((((((True ∨ (False ∨ ((True → p4) ∨ (False ∧ p1)))) ∧ p3) → (False → (p2 → p2))) ∧ p5) → p5) → p1) ∨ p1) ∨ (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669181294684190607008437744829 : ((((((False ∨ p2) ∧ (((p2 ∨ False) ∨ p4) ∧ (((p1 → (False → True)) → (p3 ∨ p2)) → (p5 → p3)))) → p5) ∨ (p2 ∧ (True ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319629422614362131551451739540 : (p4 ∨ (((p1 → (p5 ∨ (False → (True ∨ p4)))) ∧ False) ∨ ((p1 ∨ (((p2 ∨ (p3 ∨ False)) ∨ True) ∨ (((p1 ∧ p2) → True) ∧ True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_53431796155555583772696122820 : ((((True ∧ ((p1 → p5) → True)) ∨ (p2 → ((False → True) → p5))) → (((p1 ∨ (((p1 → p4) ∨ (p3 ∨ p3)) ∨ False)) ∨ p4) ∨ True)) ∨ p1) := by
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
theorem thm_5_vars_48646799662410766993578952998 : ((((p2 ∧ ((p5 → (p1 ∨ p5)) → ((p5 → p5) ∧ ((p2 ∨ p3) ∨ p5)))) ∧ ((False ∧ (True ∨ p4)) ∧ p4)) ∧ ((False → p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184863332300276691108377207536 : ((((p4 ∨ p4) ∨ True) ∧ ((False ∨ (p3 ∧ (True ∧ p4))) ∧ True)) ∨ ((True ∧ ((p2 → True) → (p4 → ((p1 → p5) ∨ p4)))) ∨ (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42882138668273989748653415615 : (((p3 → ((p2 ∧ (((((((p5 ∧ (p2 ∨ (p5 ∧ p3))) ∨ p4) → p5) ∧ ((p1 → p3) ∨ p3)) ∨ p4) ∧ p3) → False)) ∧ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172469476427707460650204973951 : (((((False → p1) ∨ p3) ∧ p2) → ((p1 → (((False → p3) → p3) ∨ p3)) → p1)) ∨ (p3 → (p3 → ((((p4 ∨ p3) ∨ False) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209033896649204689420089410112 : ((False ∨ (p4 → ((True → p5) → True))) → (p1 ∨ (((True → False) → ((p5 ∧ False) → p2)) ∧ ((True ∧ p2) ∨ ((p2 ∨ (True → p5)) ∨ True))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354783598966084165652106388077 : (p5 → ((((p3 → ((p4 ∨ p2) ∨ p1)) ∧ (p2 ∧ p3)) ∨ ((p2 ∧ ((True ∧ (True → False)) ∧ (p3 ∧ p4))) ∨ ((False ∨ True) → True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167557903717722808713862634322 : ((((((((p4 ∨ p5) ∧ False) ∧ ((True ∨ p5) → p3)) ∨ p1) ∨ p3) → p2) ∨ (False ∧ p1)) → ((p2 ∨ p2) → (((p4 → False) ∧ p4) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208034392264524571105745169547 : (((p1 ∧ (p5 ∨ p5)) ∨ (False ∧ p3)) → (((p4 → p4) ∨ p5) → ((True → (((p3 → (p4 ∧ p1)) ∨ (p3 ∨ p1)) ∧ False)) ∨ (False → True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303979907212726210689454949361 : (p1 ∨ (((p2 ∧ p1) ∧ (False ∨ (True → (False ∨ (((p5 ∧ ((p1 → (p1 ∨ ((p5 ∧ (False ∧ p3)) → p4))) ∧ p1)) → p5) ∨ p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56601822432163874263873395823 : (((p4 → ((True → True) → p3)) → (p1 ∧ (p4 ∧ (p5 ∨ (((p3 ∧ (True ∨ (p4 → p5))) ∨ p3) ∨ ((False ∧ p3) ∧ (True ∧ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166830545354351451414099139671 : (((((p1 ∨ (p2 ∨ False)) ∨ ((p2 ∧ (False → ((True ∧ p5) → p4))) ∧ p5)) ∨ p5) ∧ p2) → (p3 ∨ (True → (p3 → (p5 → (False ∨ p5)))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h24 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- Implications on the right can always be decomposed.
    intro h26
    -- Implications on the right can always be decomposed.
    intro h27
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206164081815188913898033551803 : ((p5 ∧ ((p2 ∧ (p3 → p4)) → p4)) ∨ (((((p4 → (((p1 ∨ p1) ∨ p4) ∧ p3)) ∨ p3) ∨ ((False ∧ True) ∨ (p4 → True))) ∨ p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44082695869911328530451217870 : (((((False ∧ (p3 → p4)) → (((p4 → p4) → ((p2 ∨ (p1 ∧ p4)) ∨ (p1 → p1))) ∨ (True ∧ p2))) ∧ ((p4 ∧ True) → p5)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60279374443882616626009382154 : (((False → p5) → (((True ∨ p3) ∧ (((False ∨ (False → (p5 ∧ False))) → (((p5 ∧ p1) ∧ p4) ∨ (p5 ∧ p2))) ∧ False)) ∨ (True ∨ p3))) ∨ p2) := by
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
theorem thm_5_vars_349726594250781009395024631222 : (p4 → (((((False ∧ p2) ∨ p3) ∧ (p3 ∨ (p2 → (p2 → p1)))) ∨ ((p2 ∨ (True → p4)) ∨ (((False ∨ (p1 ∨ False)) → p3) ∧ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197800034691583414818783967419 : ((((p3 ∧ p2) ∨ p2) ∨ ((True ∧ p3) ∨ p3)) ∨ (((p3 ∧ (p3 ∧ (p3 ∧ (((p2 ∨ (False ∧ p1)) ∨ False) ∨ p2)))) ∧ (False ∧ p5)) → p3)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h3.left
        let h14 := h3.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47312866558040838933419246558 : ((((p5 ∧ (p2 → p3)) ∨ (((p5 → p1) → (p1 ∧ p2)) → (((p2 ∧ ((p1 → (p3 → p4)) → True)) → p5) ∨ False))) ∨ (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37402883526315008787278759972 : (((((((p3 ∧ False) → p2) ∧ (((p4 ∨ ((p2 → p1) ∧ True)) → (p5 → p4)) ∧ (p4 ∧ (p1 → p5)))) ∧ (p2 ∨ p2)) ∨ False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39623306984225695075460644989 : (((p2 ∨ (p3 ∨ (p2 → ((((p1 ∧ (False ∨ (p1 ∧ (True ∧ ((p5 → (p1 → False)) ∧ (p2 → p3)))))) → p4) ∧ False) ∨ True)))) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697514659983604379265891252501 : ((((p4 ∧ (p3 ∨ (((((p1 ∧ p1) → p1) ∨ p2) ∨ True) ∧ False))) ∧ ((((p4 ∨ p5) → p5) ∧ ((p2 → (p4 → p1)) ∧ p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350253715325054844523837350893 : (p4 → ((p1 ∧ (((((p1 → (p3 ∨ p2)) → p5) → p5) → (p2 ∨ (p1 ∧ ((((p2 ∧ p1) ∨ p3) ∧ (False → False)) ∧ p2)))) ∨ False)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41079246265927984071318726505 : ((((p5 → (((p2 ∨ p2) ∧ ((p1 ∧ p4) → p5)) → (((((p5 ∨ True) ∨ False) → (p2 ∧ p2)) ∨ p2) ∧ p5))) → (False ∨ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215106863080246370575002254612 : (((p2 → True) → (p2 ∧ p4)) ∨ ((True ∨ (False ∧ ((p1 → (p3 ∨ (p5 ∨ (False ∧ p3)))) ∧ ((True → (p3 ∨ True)) ∧ False)))) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86293201123657904671172824209 : (((True → ((p4 → ((True ∧ (p3 ∨ p4)) ∧ p2)) ∧ p3)) ∨ ((((True ∧ (p1 ∧ p3)) ∧ False) ∨ ((p5 ∧ False) ∧ p3)) ∧ (p3 → False))) → p3) := by
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
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113523590729072763377197773374 : ((((((p3 → (False ∨ p1)) ∧ p2) ∨ (p3 → False)) ∧ (((p5 ∨ ((True ∧ p1) ∨ False)) ∨ (p4 ∧ True)) → p4)) ∨ (p5 → p5)) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174624139535035113441396420192 : ((((p4 ∨ p3) ∧ (p2 → True)) → ((((True ∨ (p1 ∨ True)) → p4) ∨ p1) → p2)) → (((p3 ∧ (p1 → p3)) ∨ (p4 ∧ (p4 ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323942341585942258914186327259 : (p5 ∨ ((p5 ∧ ((True → p4) ∧ (p2 ∧ ((p2 ∧ p3) ∨ (p4 ∧ ((p3 → True) → True)))))) → (((((p3 ∧ p4) ∧ True) ∧ p1) ∧ False) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747941561651252736258684353244 : ((((False → p5) → (p5 ∨ (((p2 → (((p2 → p2) → p1) → (((p5 ∧ (p3 → p5)) ∨ p2) → False))) ∨ ((True ∨ False) ∧ p5)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342883057979719487943887179575 : (p2 → ((((True ∧ p1) ∨ (p1 ∨ p5)) ∧ True) → ((((False ∨ ((p2 ∧ ((False → True) ∨ p5)) → False)) ∨ False) ∨ (p2 ∨ (p5 → p5))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205639808399563304800387199893 : (((p4 ∧ p2) ∨ ((p2 ∧ True) ∧ p5)) ∨ (p5 → ((True ∨ (((True ∨ (p2 → (p2 → p2))) ∧ p4) → (p4 ∨ p1))) → (p2 ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183941523674362537225676728244 : (((p1 ∨ ((p4 ∨ p3) ∧ (p2 ∨ ((p4 → p5) ∨ p2)))) ∧ p4) ∨ (((p1 ∧ ((p2 → ((p4 ∧ p3) ∨ p2)) ∧ False)) ∨ (False ∧ p4)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158149328234575897718660503132 : (((p4 ∧ ((p1 ∨ True) ∧ p2)) ∨ (p1 ∨ (((True → (p4 ∧ p5)) ∧ (True ∨ p1)) ∧ (p1 ∧ p3)))) ∨ ((p2 ∨ (p2 ∧ (True ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193273102464423393599007355484 : (((p5 → (p5 → True)) ∧ (p4 ∧ ((True ∨ p4) ∧ True))) → ((p3 ∧ ((p4 ∧ (((p4 ∨ (p4 ∨ True)) → p3) ∨ (p5 ∨ False))) ∨ True)) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65168912468797717300208491923 : ((p3 ∨ ((((p1 → p3) ∧ ((False ∧ ((p2 ∨ p3) ∧ p3)) ∨ ((((p1 ∨ True) ∧ p4) ∧ (p2 → False)) ∧ p4))) ∨ (False ∨ True)) ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732911731138956777815029911085 : ((((p2 ∧ p2) ∧ (((p2 ∨ (p5 → False)) ∧ (p5 ∨ ((((p2 → (((p4 ∧ p1) ∨ True) ∧ (p2 ∧ p5))) ∨ p5) → p5) ∨ p2))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739149425273134387566567454025 : ((((p4 ∧ True) ∨ ((p4 ∨ (((p1 ∧ p4) ∧ True) ∧ (p2 ∧ p3))) ∨ ((((p2 ∧ p1) ∨ (True → p4)) → True) ∨ ((False ∨ p5) → p5)))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113881891432838309778775664983 : ((((p2 → (p4 ∧ (((p1 ∧ p1) ∧ p4) ∨ ((p1 ∧ (p1 ∧ ((p2 ∧ p2) → p1))) ∧ p5)))) ∧ False) ∧ ((p2 ∨ p4) ∧ True)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173082330076138902126188119373 : ((p1 ∨ (((True ∨ True) ∧ (p4 ∨ (p2 ∧ (((False ∧ p1) ∨ p3) → True)))) → p1)) ∨ (((((p4 ∨ (p3 ∧ p1)) ∨ p3) ∧ True) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797417096722139004151193950818 : (((p1 → ((p1 ∧ ((((p1 → (((((p3 ∧ p4) ∧ ((p4 → True) ∨ p1)) ∧ p2) ∨ (p3 → p2)) ∨ p4)) → p3) ∧ p2) ∨ True)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248707863728504298563533895680 : ((p3 ∨ p2) ∨ (((p2 → p3) ∨ (p4 ∨ ((p2 ∧ p4) ∧ p2))) ∨ ((p2 ∧ p5) → (((p2 ∧ False) ∨ ((p1 → True) → False)) ∨ (p2 ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68852240406728065673475794285 : ((p4 → ((p4 → p2) ∨ ((((p2 ∨ p3) → ((True ∨ p5) ∧ (p2 ∧ (p5 ∧ ((True → p1) ∧ p2))))) ∧ p3) ∧ ((p3 ∨ p1) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64254047593359332135614443277 : ((False ∨ (p3 ∨ (p2 ∧ ((p3 ∨ (p5 ∨ False)) ∨ (((p4 ∨ ((((p5 → ((p3 ∧ False) → p3)) → False) ∧ False) ∨ p1)) ∨ False) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149459852055654118665697998778 : ((False ∧ (((((p5 ∨ (p3 ∧ (False ∨ False))) → p4) → p3) ∧ p2) ∨ ((p3 ∨ p3) ∧ ((p3 → p4) ∨ p4)))) ∨ (p3 → (p4 ∨ (False → True)))) := by
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
theorem thm_5_vars_52261517796449932843883321038 : (((p4 ∨ ((((p1 ∧ p5) → False) ∨ ((((False ∧ False) ∧ False) ∧ p3) ∧ False)) → p5)) → ((((True ∨ p2) → p5) ∧ (p3 ∨ True)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171509220521790579989863152799 : ((((((p3 ∨ False) → (p1 ∨ (p2 ∨ (p5 → p3)))) ∧ (False ∧ p4)) ∧ True) ∨ p1) ∨ (((p4 ∧ p2) ∧ (((p2 ∨ p3) → p4) → False)) → p3)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∨ p3) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h6
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48573328241159001628112108274 : ((((p2 ∧ ((((p1 → False) → ((False → (p2 → (False ∧ False))) ∨ (p2 ∨ p5))) ∨ True) → (p3 → p2))) → p1) ∧ ((p5 ∧ p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706116087998743090062480883573 : (((((p1 ∧ p5) → (((p3 ∧ False) ∧ False) ∧ False)) ∧ ((((p2 ∧ (p4 → (False ∨ ((p5 → p1) → (p2 ∨ p4))))) ∧ p1) ∨ p5) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50536225268602467690880917004 : (((((((True → (False ∨ (True ∨ p5))) ∧ (False ∨ (p1 ∨ True))) ∨ (p2 → False)) ∧ (p1 → p2)) ∨ p3) → (((p5 ∨ p1) → True) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195187049548158625833050210823 : (((((p4 → True) → p5) ∨ p1) ∨ (p5 ∨ True)) ∧ ((((((p5 ∨ False) ∧ p4) ∨ p4) ∧ p1) ∨ (p3 ∨ (p2 ∧ p3))) ∨ (p3 ∨ (True ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130845949343764694627954078076 : (((p3 ∨ (p1 → (((((p3 ∧ False) → True) → p4) ∨ True) → (p1 → p5)))) → ((p5 ∨ (False → (p2 ∨ False))) ∨ p4)) ∧ ((True → p5) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104514124710315764401562425231 : (((((((True → p1) → False) ∨ False) → ((p4 → ((p1 ∧ ((p1 → True) → p4)) ∨ (p2 → False))) ∨ p5)) ∨ False) ∨ (True ∨ p4)) ∧ (True ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157767061891969007201355380450 : (((p5 ∨ ((True ∨ False) → (p5 ∨ (p4 ∧ ((p4 ∧ False) → True))))) ∧ (((p5 ∨ p3) ∨ True) ∧ False)) ∨ (((p2 → True) ∨ False) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157895581174038665043116998336 : ((((((p5 → p4) ∧ ((p2 ∨ True) → p5)) ∨ p4) ∧ p4) → ((True ∨ p1) → ((p3 ∨ p1) ∨ p5))) ∨ ((False ∨ p5) ∨ ((True ∨ p5) ∨ p4))) := by
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
theorem thm_5_vars_316939554329928017145031951393 : (p3 ∨ (p2 → (((p5 → (False ∧ p2)) ∨ (False → p3)) → ((p5 ∨ ((True ∨ p4) ∧ ((p3 ∨ False) ∧ p5))) ∨ (False → (p4 ∧ (p5 ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
theorem thm_5_vars_49241762941848744863641724561 : ((((p2 ∨ p2) → (p3 → ((((False ∨ p1) → False) ∨ (p3 ∨ p5)) ∧ ((True → (p3 ∨ p2)) → (p2 → p5))))) ∨ (False → (p5 → p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171504054444596717725590056031 : (((((False ∨ ((p4 → ((p2 ∧ (p2 ∧ p4)) ∨ p1)) → p1)) ∧ True) ∧ p3) ∨ p1) ∨ (p5 ∨ (False → ((p2 → ((p4 ∧ False) ∨ True)) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223520455344666641599412945319 : ((False ∨ (False → True)) ∧ ((p5 ∧ p4) → ((p2 ∧ (((p5 ∨ p2) ∨ p3) ∧ ((p1 ∧ (True ∨ (p3 ∨ True))) ∨ True))) ∨ ((p3 ∨ p2) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245552663655301262344547259645 : ((p3 ∧ True) ∨ ((False → (p5 ∧ (p3 ∧ p1))) ∧ ((((p5 ∨ p5) ∨ True) → p3) ∨ ((True ∨ (p4 ∧ True)) ∨ ((p3 ∧ (p4 ∧ p3)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259661212325101565809970006495 : ((p1 → False) → (p5 ∨ ((((p3 ∧ (((p4 ∧ (p3 ∧ ((((p5 ∨ p5) → p2) ∧ p4) ∨ p3))) ∨ p4) ∧ (p2 ∧ p4))) ∧ p1) → False) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h8.left
      let h18 := h8.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h8.left
      let h23 := h8.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h24
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h8.left
    let h28 := h8.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h29 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h30 := h1 h29
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217803743555695528496258861094 : (((p1 ∨ (False → False)) → False) → (((p3 → p3) ∨ (p1 ∧ (p4 ∨ ((((p3 ∨ (p3 ∧ False)) ∧ True) → p5) ∧ p4)))) → ((False ∨ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∨ (False → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ (False → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : (p1 ∨ (False → False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h19
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : (p1 ∨ (False → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h27 := h1 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h31 : (p1 ∨ (False → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h32 := h1 h31
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165550606122489225321693186601 : ((((False ∧ p1) ∧ ((p5 ∧ (p2 ∨ p4)) ∨ True)) ∧ ((p4 ∨ ((p2 → False) ∨ p4)) ∨ False)) ∨ (False → (True ∧ (p2 ∨ (p2 ∨ (True → p3)))))) := by
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
theorem thm_5_vars_347656982167566923415529398612 : (p3 → (((p1 ∧ False) ∨ (p4 → False)) → ((((False ∨ (p3 ∨ p4)) ∧ (((True → p4) → ((p1 ∨ False) ∧ p2)) ∧ True)) ∨ p1) ∧ (p3 ∧ p3)))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- False on the left can always be used.
    apply False.elim h11
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h14 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h15 := h6 h14
    -- False on the left can always be used.
    apply False.elim h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621094184416713753444201497274 : (((((p3 → p2) → ((p5 ∨ ((p5 → (((p4 → ((p4 ∧ p4) ∨ p3)) ∨ False) ∧ p1)) ∨ ((p4 ∧ False) ∧ (p4 ∨ False)))) → p2)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37733175002811227470670256376 : (((((p4 ∧ ((p5 → p5) ∨ (((p3 ∧ p4) ∧ p5) ∧ p4))) ∧ (p5 ∨ (p5 → ((p4 ∧ ((p3 ∨ p5) → p4)) ∨ p1)))) → p5) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105692410001365836845676124867 : (((((((p2 → True) ∨ p3) → (p1 ∧ ((True ∧ p2) ∨ (True → p4)))) ∨ False) ∧ p4) ∨ ((p3 → p4) ∨ (True ∨ (p1 ∨ False)))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344438879198208148430858403804 : (p2 → (p5 ∨ ((p5 → (p3 ∨ p4)) ∨ ((((True ∧ (False ∧ p3)) ∨ (p3 → (False → p3))) ∨ (p5 → (p2 → p3))) ∧ ((p3 → p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133990178942013347214629236103 : (((((p4 ∧ ((False ∨ (((True ∨ ((False ∧ False) → p1)) → p3) ∨ p2)) ∧ p3)) ∨ ((p5 ∧ p4) ∧ False)) ∧ True) ∨ p1) ∨ (p3 → (True ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622645596914686587729966079944 : ((((p4 ∧ (((((True ∨ p4) → ((p4 ∨ (True → (True → False))) → p2)) → (p2 → True)) ∨ (p3 ∨ p5)) → (False ∨ (p4 ∧ p1)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_48727226130685431086088868341 : (((((p5 → p3) ∧ p4) ∧ ((p2 ∨ (p5 ∧ (p3 ∧ (p5 → p2)))) ∨ ((p4 ∧ (True ∧ p4)) → (p4 → p2)))) ∧ ((p5 → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111633988626676660337045162263 : ((((((((((False ∨ p1) ∧ p1) ∧ p1) ∨ p5) ∨ (p3 ∨ p3)) ∨ p3) ∧ (p1 ∨ (p4 → ((True ∧ p2) ∨ p4)))) ∨ p1) ∨ p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57972924934541291791222532853 : (((p3 → (p3 ∨ True)) → (((p1 ∨ p4) ∧ (True → (((p1 ∨ p5) ∧ (((p2 → p5) ∨ (p5 ∧ p5)) → p2)) ∨ p5))) ∧ (p3 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136100881852313363825641387964 : ((((True → ((p2 → (p2 ∧ p1)) → True)) → False) ∨ (((p5 ∧ (True → False)) ∨ p1) ∨ (p4 ∨ (p1 ∨ (p1 ∨ p3))))) ∨ ((p1 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184899917928423269380116384010 : ((((p3 ∨ False) ∧ p1) ∨ ((p4 ∨ ((p4 ∧ False) ∧ p1)) ∨ True)) ∨ ((p4 ∨ False) ∧ ((p2 ∨ p5) ∧ (((p5 ∨ p5) ∧ p1) ∧ (p3 ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207049992836133907402248561312 : (((True ∧ (p4 ∨ (p3 → False))) ∧ p4) → ((((((p5 ∧ p3) ∨ ((p2 ∧ (p1 → True)) ∧ True)) ∨ (p5 ∨ False)) ∨ p4) ∧ (False → p3)) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165700880753340240309539019566 : (((((False → p5) ∧ p3) ∧ p2) ∧ (((False ∧ (p4 ∨ (p2 ∧ p5))) → (True → p4)) → p5)) ∨ ((p3 ∨ (((p1 → p3) ∨ True) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323718457559942098779646394262 : (p5 ∨ ((((True ∨ p5) ∨ (p3 → p2)) ∧ (p5 ∧ (p3 ∨ ((p2 → False) ∧ (((False → p2) → p3) ∨ False))))) → ((False ∧ p5) ∨ (p1 → p3)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h15 : (False → p2) := by
            -- Implications on the right can always be decomposed.
            intro h16
            -- False on the left can always be used.
            apply False.elim h16
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h17 := h13 h15
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h29 : (False → p2) := by
            -- Implications on the right can always be decomposed.
            intro h30
            -- False on the left can always be used.
            apply False.elim h30
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h31 := h27 h29
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h3.left
    let h35 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h37
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h42
        -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
        have h43 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h44
          -- False on the left can always be used.
          apply False.elim h44
        -- We have shown the premise of h41, we can now drive its conclusion.
        let h45 := h41 h43
        -- One of the premise coincides with the conclusion.
        exact h45
      case inr h46 =>
        -- False on the left can always be used.
        apply False.elim h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135785352400454658854890239871 : ((((((p5 → (p3 ∧ p5)) → (p2 → True)) → False) ∨ (p2 ∨ (p1 ∧ p5))) → ((p1 ∨ False) ∧ (p1 ∨ (p2 → p1)))) ∨ (p2 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



