variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115078643813745425511571146502 : (((False ∧ (True ∧ ((True ∧ p3) ∧ (p2 ∨ (p2 ∨ (p3 ∧ p4)))))) ∨ (True ∧ (p2 → ((((True ∨ True) ∧ p1) ∧ True) ∨ p3)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748463052606214001467140856315 : ((((p2 → p5) → (((p5 → ((p1 ∧ p2) ∧ ((False ∧ p2) → True))) → (((p2 ∧ False) → False) ∧ ((p5 → (p1 ∧ p3)) ∨ p5))) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177306892062445299452730820101 : ((p2 ∨ ((((p2 ∧ ((p3 ∨ True) ∨ p4)) → True) ∨ (p3 ∨ False)) ∨ False)) ∧ ((((p2 ∧ (p2 ∨ p5)) ∨ p5) ∨ (p4 → True)) → (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40768660957614503289806159523 : (((((p5 ∨ p5) → ((((p5 ∧ (p4 ∧ p3)) → p4) → (p5 → (p5 ∧ ((((p3 ∧ p1) → False) ∨ True) → p3)))) ∨ p4)) → p3) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192745431399090938052679735060 : ((((False ∧ p2) → ((True → (p3 ∧ p4)) ∨ p4)) → True) → ((True ∧ (((p2 → p2) → (p1 → p1)) → (p2 ∨ (p5 ∨ p3)))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37139192505857208083646401884 : ((((((((p4 ∧ (True → (p4 → (p5 ∨ ((p4 ∨ False) ∨ (p3 ∨ p3)))))) ∧ p3) ∧ (True ∨ p1)) → True) → (p4 ∧ True)) ∧ p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451802107757523108768385158893 : ((((((p1 ∨ (p4 ∧ (p5 → p3))) → False) ∧ ((p5 ∨ ((((True → p4) ∧ p4) ∧ p4) ∧ p1)) ∨ p4)) ∨ (p2 ∨ (p4 → (p1 → True)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65223181600892544150182169926 : ((p3 ∨ (((p5 ∧ p5) → (((p1 → (False → True)) → p2) ∨ ((p1 → ((p4 ∨ (p2 ∧ True)) ∧ ((p4 ∨ p2) ∧ False))) ∧ p5))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216487671420277901800199004166 : ((p5 → ((p5 ∧ p2) ∨ p3)) ∨ (True → ((p1 ∨ False) → ((p5 ∨ (((p4 ∨ ((p5 → p4) ∨ p4)) ∨ p1) ∧ (p5 → (p4 ∨ False)))) ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58705186985480039935199315368 : (((p2 → p5) ∧ ((p5 → ((p1 ∨ False) ∨ ((((False → True) ∨ False) → (True → (p1 → (True ∧ p1)))) ∧ p5))) ∧ (p4 ∧ (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134321927194408986847044495623 : (((p1 ∧ (True ∧ (p3 → ((False ∧ (p4 ∨ ((p2 ∨ (p2 ∧ True)) ∨ (False ∧ p3)))) ∨ ((p2 ∨ p3) ∨ p3))))) ∨ True) ∨ (p1 ∨ (p3 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339007798433197233692487675773 : (p1 → (True ∧ ((p4 ∧ ((((p3 → (True ∨ p4)) → (False ∨ False)) → p5) → ((((p5 ∨ True) ∧ p3) ∧ p5) ∧ (p2 → p3)))) ∨ (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341836467631209712971223457659 : (p2 → (((((True ∧ p4) ∧ ((p5 ∧ p4) ∨ p2)) ∨ False) ∨ ((((False ∨ p5) → p5) ∨ (p5 → p1)) ∧ (True ∨ (False ∨ True)))) → (p1 ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
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
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234065712448691387484202592326 : ((True → (True ∧ p2)) → ((p1 ∨ (((p1 ∧ p5) ∨ (p5 ∨ ((True ∨ p2) ∧ ((p2 ∧ (p2 ∨ False)) → (True ∨ p4))))) ∨ (p2 ∧ p2))) ∧ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324478378662256756820089442823 : (p5 ∨ (((p1 → (True ∧ p4)) ∧ p4) ∨ ((p3 ∨ (p3 ∧ (p5 ∧ p2))) ∨ ((p4 → ((((p5 ∧ p2) → p5) → False) ∨ True)) → (p2 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749172590465475802619265451578 : ((((p5 → p2) → ((p5 ∧ (((False → (False ∧ p3)) → False) ∧ ((p2 → (False → False)) → ((((False → p3) → p3) ∧ p3) ∨ p3)))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213908590647626967314646732000 : (((p5 ∨ (p5 ∧ p1)) ∨ p2) ∨ ((p3 → (False ∧ (((p5 ∧ p3) ∨ p2) → (((p5 → ((p5 ∧ p3) → (False ∨ p1))) → p2) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219584139938122394654204947046 : ((True → (False ∧ (p2 → p4))) → ((((((p1 → p4) → p1) ∨ ((p2 ∨ True) ∨ True)) ∧ p2) → ((p3 ∨ (p3 ∧ p5)) → p1)) ∨ (p5 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252476908586699856293587375323 : ((p5 → p1) ∨ (((p2 ∨ p3) → (p4 ∧ p5)) → ((((p1 ∧ p3) ∧ (p4 ∧ (True ∨ p5))) → ((True → ((True → p1) → False)) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1456127972354354937431131163 : (((((((True → p1) ∨ ((p4 ∧ (p3 → ((p4 ∧ p1) ∧ p2))) ∧ p2)) ∧ ((False → p3) → True)) ∨ p4) ∨ p4) ∧ False) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260828907042851287834902130978 : ((p4 → True) → (((p5 → (p1 ∨ (((((p5 ∧ (p1 ∨ p4)) ∨ p1) ∨ p4) ∨ (p1 ∨ (p2 ∨ p5))) ∨ (p5 ∧ p4)))) ∨ (p3 ∧ p1)) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199864298665259027764268359928 : (((p5 ∨ ((p1 → p5) ∨ p4)) ∧ (p1 ∧ p1)) → (((p4 ∨ ((((True ∨ p2) ∨ ((p3 → (p5 ∧ p5)) ∧ p3)) ∧ True) → False)) ∨ True) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342045631738508525021188898246 : (p2 → (((p1 → (p3 ∧ (((p2 ∧ (p3 → False)) ∨ False) ∧ (p4 ∨ (((p2 ∧ p5) → p2) ∧ p1))))) ∧ (p1 ∧ p2)) → ((p1 → p5) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116551368379483117151051094722 : (((p1 ∨ p1) ∧ (((((False ∧ ((True ∧ (True → (p1 → False))) ∧ p1)) ∨ p5) ∨ (p3 ∧ True)) ∧ (p4 ∨ (p3 ∧ True))) ∧ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58628406998511022747836914726 : (((False → p5) ∧ ((p5 → p4) → (False ∨ (False ∧ (((p2 → p2) ∧ p1) → ((p4 → p1) ∨ (p2 ∨ ((False ∨ p5) → (p5 → p4))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113513072195911519844568292532 : (((((p1 ∧ (p3 ∧ ((p2 ∨ False) ∨ (p4 ∧ p5)))) → (p2 ∧ p2)) ∨ (((p5 → False) ∧ p4) ∧ (False ∧ True))) ∨ (p3 ∨ p1)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315414200616291847194027017481 : (p3 ∨ (((p3 ∨ True) → p1) ∨ ((False ∨ ((p4 ∧ (p2 ∧ ((((p2 → ((p1 → True) → True)) ∨ p5) ∧ p3) ∧ p5))) ∨ p1)) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301159688976888424585609164563 : (False ∨ ((False ∨ ((p1 ∨ ((True ∧ p3) ∧ p1)) ∧ p4)) ∨ (p4 ∨ ((True → ((p5 → True) ∨ (p2 → p2))) ∨ (p5 → (p2 ∧ (p3 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652131211547696510820802265283 : ((((p1 ∧ (((((p4 ∧ p3) → False) → ((p1 → p3) ∨ (p2 ∨ p4))) ∧ False) ∨ ((p3 ∧ (p3 ∧ (p3 ∨ p4))) ∨ p5))) ∧ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613408260115556538123564711967 : (((((p4 ∧ ((p3 ∧ ((((p5 ∨ p2) → p5) ∨ False) ∨ (True ∨ ((p2 → True) ∧ p5)))) → ((p1 ∧ False) → p1))) → (p3 ∨ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169390253792582870917943537968 : ((((((p3 ∧ True) ∧ ((p2 → True) → p4)) ∨ ((p5 ∧ p2) ∨ True)) ∨ p3) ∨ False) ∧ (((p1 → True) ∨ p1) ∨ (False → (p3 ∧ (p1 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258293799150512190102114132252 : ((p5 ∨ True) → ((((True ∧ p1) ∨ p3) → (((((p4 ∨ (p2 ∨ p3)) ∧ p4) → p1) ∧ (p2 → False)) ∨ (True → True))) ∨ (p5 ∨ (p4 → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480270865557737797264609042316 : ((((((p5 ∧ p3) ∨ ((False ∧ p5) ∧ p2)) ∧ True) ∨ ((((p2 → (p1 ∧ p5)) ∧ (p4 ∧ p3)) ∧ (((p5 ∧ p3) → p3) → p2)) → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∧ p3) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h8
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h14 := h4 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- One of the premise coincides with the conclusion.
  exact h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617632954886428767842112426198 : ((((((p3 ∨ ((False ∧ p1) ∧ p5)) ∧ p3) ∨ ((p4 ∨ ((p5 ∨ False) → ((((p3 ∨ p4) ∨ p1) ∧ True) ∧ (p2 ∧ False)))) ∧ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_157098450398951563431944816164 : (((p1 → (((p5 ∧ (True ∧ (p2 → p1))) ∨ p4) ∧ (p3 → (((p4 ∨ p5) → p5) ∨ p4)))) ∨ p3) ∨ (True ∨ ((True ∨ p3) → (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262344874190546305970992848150 : (True ∧ ((((p5 → (False ∧ p3)) → p3) ∨ ((p3 ∧ p5) → (p5 → ((p2 ∨ (((p2 ∨ p4) ∧ False) ∧ (p5 → (p4 ∧ True)))) ∧ p5)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704935804202102944028712961366 : ((((p5 ∨ (((p5 → (p2 ∨ p5)) → (p5 ∨ False)) ∨ p1)) → ((p4 ∨ (p1 → (p1 ∧ (p2 ∧ p1)))) ∨ (False → ((False ∨ p3) ∨ p2)))) ∨ p2) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234869392191754212124198803998 : ((p5 → (p2 → p1)) → (((True → ((p4 → p5) ∨ False)) → p5) ∨ ((True ∧ (((True ∧ (True ∧ (p2 ∨ p2))) ∨ p5) → (False ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149459748909306028620736574942 : ((False ∧ ((False ∨ (False → (True ∧ (((True ∨ p1) ∨ p4) ∧ p1)))) ∧ (False ∧ ((p2 ∧ (False ∧ p2)) ∧ True)))) ∨ (p4 ∨ ((True ∨ False) ∨ p4))) := by
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
theorem thm_5_vars_464668424513548055290277735136 : (((((p1 ∧ (p4 ∨ (p4 → (p3 → p5)))) ∨ ((p4 ∨ p2) → (p1 ∧ (True ∧ True)))) → (p5 → (p5 → ((False ∧ p3) ∨ (p5 ∨ False))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300120647929015857781774811959 : (False ∨ (((True ∧ (p1 ∧ p1)) ∧ (((p4 → (p1 → p1)) → (p2 ∨ ((p1 → p1) ∧ (((False ∧ False) → p2) → p4)))) ∧ True)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197119708595481851200393186724 : (((p2 ∨ ((p3 ∨ (p1 ∨ p3)) ∧ p1)) ∨ p3) ∨ ((True → (False ∨ ((((p3 ∨ p4) ∧ p1) ∨ ((p1 ∧ p1) ∧ False)) ∨ (p4 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927983333170334600877520865720 : (((((True ∧ (True → p4)) ∧ (True ∧ ((p3 ∧ p2) → False))) ∧ (False ∨ ((p1 ∨ (p2 ∧ (p3 ∧ p1))) → ((p2 → (p4 ∨ p2)) ∧ p1)))) → p4) ∧ True) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320308408927505390352958332373 : (p4 ∨ ((False ∨ p3) ∨ ((((p5 → p3) ∧ p4) ∨ True) ∨ ((p3 ∨ True) → ((((False ∧ (False ∨ (False ∨ p2))) ∧ (True ∧ p5)) ∨ p5) → p2))))) := by
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
theorem thm_5_vars_148388021444132039004813217496 : (((((p2 → True) ∨ p1) → ((p3 ∧ ((p2 ∨ (p5 → p5)) → p3)) ∨ True)) ∨ (p5 → (p3 ∨ (p2 ∨ p5)))) ∨ (True ∧ (p4 ∧ (p4 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_218573463721162205188148363983 : (((p1 → p2) → (p4 → p2)) → (p4 → (p3 → (((((p4 ∨ (p3 ∨ (p3 → p1))) → p3) → ((p4 → p5) → False)) ∨ p4) ∧ (p2 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169382308521090666364250801445 : ((((((p5 ∧ False) ∧ (p3 ∧ (p3 → ((p5 ∨ p5) ∧ p3)))) ∧ p1) ∨ p1) ∨ True) ∧ (((p5 ∨ True) ∧ (True → p1)) ∨ ((False → p1) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349081295425812803233987862570 : (p3 → (p5 ∨ (p2 → (((((p2 ∧ (p1 ∧ p5)) → (p2 ∧ ((p3 ∧ p2) → (p2 ∨ (p3 → (p2 → (True ∨ p2))))))) ∨ p3) → p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711621100185651299502480912773 : ((((p3 → (((p5 → p2) ∨ p3) ∧ True)) ∧ (((True ∧ (p4 ∧ ((p3 → (((p2 ∨ (p2 ∧ p4)) → True) ∧ p4)) → p5))) ∨ True) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66296856232517129644847469084 : ((p5 ∨ ((p2 ∨ p2) ∨ ((p4 ∨ ((True ∧ (p4 ∨ p2)) ∨ (p2 ∧ (((((p4 ∧ p4) → True) ∧ (p1 → True)) ∧ p4) ∨ p5)))) ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_38346915102507576240576283684 : ((((p1 ∧ (((p2 ∧ ((True → False) ∨ p1)) ∧ p5) ∧ (((p2 → p3) ∧ p3) ∧ p1))) ∧ ((p3 → (p1 ∨ p3)) → (p1 ∧ p5))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198694797674242640669447093510 : ((p4 ∨ (p3 ∨ (p3 ∨ ((p1 ∧ p3) ∨ p1)))) ∨ ((((p5 → p2) ∨ p5) ∨ p1) ∨ (((True ∨ (p3 ∧ (False ∨ (True ∧ p3)))) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343518648370755571830922224345 : (p2 → ((p3 ∧ p2) → (p1 ∨ (((p4 ∧ ((p2 ∨ p5) ∧ ((((False ∨ (p2 → p2)) ∧ p1) → False) ∨ (p5 → (True → False))))) ∧ p4) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167277854754855934797334241418 : ((((((p4 ∧ True) ∨ ((True ∧ ((p2 → p5) ∧ (p5 ∨ p2))) ∧ p3)) → False) ∨ p2) → p5) → (((p5 ∧ True) ∧ (True ∨ (p2 → True))) → p5)) := by
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
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41137304578466560133293999235 : (((((((p2 ∧ True) → ((((False ∧ True) ∨ ((False ∨ p5) ∨ p1)) ∨ p5) ∧ True)) → p3) ∨ (p5 → p3)) ∨ ((p4 → False) → p5)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69156963635383621870204385211 : ((p5 → (((((p3 → (p5 ∧ (p2 ∧ ((p3 → False) → p3)))) ∨ (p1 ∧ (p5 ∧ p1))) → p2) ∨ p4) ∨ ((p4 ∨ (p5 → p4)) ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718755746368490850424014393546 : (((((p2 ∧ True) ∨ (p2 ∧ p5)) ∨ (((p5 ∧ (((p4 ∨ (True ∨ (p3 → (p3 ∨ True)))) → p4) ∨ p2)) ∧ p4) ∧ (True → (True → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159759956963052255913294309069 : (((((True → True) ∧ p5) → (p4 ∧ (p1 ∧ (((p1 ∧ False) → ((p4 ∨ p4) ∨ p5)) ∧ False)))) ∨ p5) → (p4 → ((p5 → p2) ∨ (False → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166038084293422620597605956970 : (((p3 → False) ∨ (p3 ∧ (((True → (p3 ∧ (p1 ∨ ((p1 ∧ True) ∨ p3)))) → True) → p4))) ∨ ((p1 ∧ ((False ∨ True) → (True → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718585698549997044618274773252 : (((((True ∧ p3) ∧ (False ∨ p2)) ∨ ((((p4 ∧ ((((True → p1) ∨ ((True ∧ p5) → p2)) → (p3 ∨ p5)) ∨ p5)) → False) ∨ p4) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621675658587151250304945648268 : ((((False ∧ (p3 ∨ (((p1 ∨ (True ∨ True)) ∨ (p4 ∨ True)) → (p4 → (p3 ∨ ((True ∨ (False → p2)) ∨ (p3 ∨ (True ∧ p2)))))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357106752014816157045145902062 : (p5 → ((False ∨ (False → p4)) → ((((((((p4 ∧ True) → ((False → False) ∧ p3)) → p2) → p2) ∧ p2) → (p4 ∨ (True ∧ p2))) ∨ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192503746858585139331522227493 : ((((p1 ∨ p4) ∧ ((p5 → (p1 ∧ True)) ∨ p5)) ∨ p4) → (((((p2 → p5) ∧ (p2 ∨ (p5 ∧ p3))) ∨ (p1 ∨ p4)) ∧ (True ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253787728662064593824556944818 : ((p1 ∧ p2) → ((p2 → ((p4 ∧ ((((False ∧ ((p5 ∧ p4) → p1)) ∧ (False ∨ (True ∨ ((p1 ∨ False) ∧ True)))) ∨ p5) ∨ False)) ∨ p2)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52265058058182352278927423728 : (((p5 ∨ ((((p4 ∨ (p1 ∨ (p2 → (p3 ∨ True)))) ∧ p5) → p2) → (p1 ∧ p4))) → ((False ∨ p1) → (((p3 → p3) ∧ p3) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51450476543920637906442136501 : (((((((p2 ∨ p3) → (True ∨ p4)) → p4) ∨ ((False ∧ p5) ∧ False)) ∨ ((p4 ∧ p2) ∧ p3)) → (((p3 ∧ p5) ∨ (p1 ∨ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300155750130599684568842287605 : (False ∨ ((p5 ∨ (((((p3 ∧ p1) → p3) → p3) ∧ p1) ∨ (False → (p4 ∨ (True → (p3 ∧ (((True → True) ∨ p4) ∧ True))))))) ∨ (True → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196931804557629829619714588585 : ((((p3 ∨ ((p5 ∧ p2) ∧ p5)) ∧ p1) ∨ True) ∨ ((((p3 ∧ ((p1 ∧ p2) ∧ p4)) → ((False ∨ p3) → True)) ∨ p3) ∨ (p5 ∧ (True ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258992710699313623927464582962 : ((True → p3) → (p4 ∨ (((((p5 ∧ p5) ∧ p2) ∧ (p1 ∧ p4)) ∧ False) ∨ ((False → (p2 ∧ ((False → True) ∧ p3))) ∨ (p5 ∧ (True → p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739025337171651662663233399410 : ((((p3 ∧ p3) ∨ (((((p5 ∨ (True ∨ False)) → ((p2 ∧ ((p1 → (p3 ∨ p1)) ∧ p1)) ∧ p2)) ∧ p5) ∧ p1) ∨ ((p4 ∧ p3) → p4))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665261901235663365052375950217 : ((((((((p2 → p5) ∨ (((True → (p3 ∨ p5)) ∧ False) ∨ p4)) ∧ True) ∧ ((p2 ∨ p5) ∨ (p2 ∨ p3))) ∧ False) ∧ ((p2 ∧ p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336084653424727552572104847438 : (p1 → ((((False ∨ ((p2 ∧ (p4 → p3)) ∧ (((p4 → p2) → p1) ∨ p4))) → (((p2 → p1) ∧ False) ∧ ((p4 ∧ False) → p3))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134609465779388555610747184201 : ((((p3 ∧ ((p5 → ((p5 ∨ ((True ∧ p4) ∧ p5)) → ((True → p3) → p4))) ∨ True)) ∧ (p1 → (p3 → False))) → p1) ∨ ((True → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305686995150415511081147303031 : (p1 ∨ ((p3 ∧ ((p2 ∨ False) ∧ (p5 → (False ∨ (True ∧ p3))))) ∨ (((((p4 ∨ p1) ∧ p5) ∧ (p4 → p5)) → ((p2 ∧ False) ∧ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116210506648698821832734162298 : ((((False ∧ p1) ∨ False) ∨ ((False ∨ (p5 ∨ (False → True))) ∧ ((p2 → True) ∨ (p3 ∨ (p1 ∨ (((p1 → False) ∨ p4) → False)))))) ∨ (p1 ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164996197463357365527034175114 : (((((p5 ∨ False) ∨ (p1 ∨ (True ∧ (p4 ∧ p1)))) ∧ (p1 → ((p4 → True) ∧ p5))) → p3) ∨ (((p1 ∨ p5) → (p5 ∨ (True ∨ p5))) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133758855085796881663164875503 : ((((((False ∨ (p3 ∧ p4)) ∨ p1) ∨ p5) ∨ ((p1 → ((p1 → p5) ∧ p4)) → ((p1 ∧ True) ∧ (False ∨ p2)))) ∧ p2) ∨ ((p4 → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300547927063033406981116626061 : (False ∨ (((((p5 → ((p3 ∧ ((True ∧ (p3 ∨ True)) ∧ False)) → False)) → False) ∧ True) ∧ (p3 → (p2 ∨ p1))) ∨ (p1 ∨ (p2 → (False → p5))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721652909957536837180606283529 : ((((True ∨ ((p5 ∨ p5) → p2)) → (((p1 ∧ p4) → False) → (((True ∨ p1) ∧ p4) ∧ ((True ∨ p5) → (p2 → (p5 ∧ (p5 ∧ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200882713627069818462564946821 : ((False ∨ (((p5 → p2) → p3) ∧ (p3 ∧ p3))) → ((((False ∨ p3) → p2) ∨ (True → ((p3 ∨ p3) ∨ False))) ∧ (False → ((True → p2) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737337260086097339785212865643 : ((((p4 → p2) ∧ ((p4 → (p2 → ((p3 → p5) ∨ ((p5 ∨ p2) ∧ (p5 ∨ p3))))) → ((True ∨ (p2 ∨ p1)) → ((False ∧ p5) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134767238770390077204275533462 : ((((p4 → p5) → (p5 → (False → (((p5 → p1) ∨ p2) ∧ ((p3 → (p2 → p1)) ∧ ((p2 ∨ True) → p1)))))) → p5) ∨ ((False ∧ True) → p4)) := by
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
theorem thm_5_vars_616430671151759858160464354601 : (((((((True ∧ ((p1 ∨ p4) ∨ p2)) → (p4 → True)) ∧ (True → p4)) → ((p1 → ((p2 ∨ ((p1 ∨ p5) → p2)) → p4)) ∧ p5)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_159221707983597023744330562645 : ((p2 → (p3 ∨ ((p5 ∧ p4) ∨ (((True ∨ (p2 → p3)) ∨ (False ∧ (p3 ∧ (p4 → False)))) → p1)))) ∨ (p5 ∨ ((p4 ∧ True) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_161329082631508571706054577361 : ((True ∧ (p2 ∧ (((p1 → ((((p4 ∧ p3) → True) ∧ (True ∨ (p1 ∨ False))) ∧ p1)) ∧ p1) ∨ p2))) → (p4 ∨ (p4 → ((p5 ∨ p5) ∨ p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40768104437575443728925732401 : (((((p4 ∨ False) → (p5 ∨ ((((((p3 ∧ p5) ∧ p2) ∨ (p4 ∧ (p1 ∧ p1))) ∧ (p3 ∧ (p4 ∨ p4))) ∨ p2) ∨ False))) → p5) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351001275685169087429572117358 : (p4 → ((False ∨ (((p1 ∨ (p3 → p1)) ∧ ((p1 ∧ p3) ∨ (True → (p3 ∧ True)))) ∨ ((p2 ∨ (p1 ∧ (p5 ∨ p2))) → p4))) ∨ (p3 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98899770283309133983952999859 : ((True → (((p3 → p2) → ((p3 ∧ p1) ∨ (((p1 ∨ (True ∨ p5)) ∨ (((True ∨ p3) → True) ∧ p3)) ∧ ((p3 → False) ∨ True)))) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 → p2) → ((p3 ∧ p1) ∨ (((p1 ∨ (True ∨ p5)) ∨ (((True ∨ p3) → True) ∧ p3)) ∧ ((p3 → False) ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305793777702983715899315020787 : (p1 ∨ ((((p3 ∨ (p2 → (p2 → p3))) ∨ p1) ∨ False) → ((p1 ∨ (((p1 ∧ (((p4 ∨ p3) ∧ p4) ∧ False)) ∨ False) ∨ p1)) ∨ (True ∨ p5)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68424206601430544768632844990 : ((p3 → ((p5 ∨ p5) ∨ ((((((p1 → False) ∨ p3) → p4) ∨ (p2 → (p2 ∧ (((p3 → p4) ∨ p3) ∧ False)))) ∧ p1) → (p3 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172957501727217541431208452259 : ((p4 ∧ (((((((p5 ∧ False) → (p3 ∨ p5)) ∧ False) ∨ True) ∧ p3) ∧ p4) ∨ False)) ∨ (((p3 ∨ (False ∧ False)) → (p3 → (False → p3))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38527308777930625644461852088 : (((((p5 → False) → ((((p2 → False) ∧ (p2 ∨ p2)) ∨ p5) ∧ p2)) → ((p5 ∨ p4) ∨ ((((False ∧ p3) → True) ∧ p1) ∧ False))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710825811822764819346225510604 : (((((p5 ∧ p4) ∧ (p5 ∨ (False ∧ p4))) ∧ (((False ∨ (True → True)) ∨ (p3 ∧ ((True ∧ False) ∨ p4))) ∨ ((p4 → (p3 ∨ p5)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10210639477906993580556191090 : (((p2 ∨ ((((((False ∧ p5) → (p5 ∨ (False ∧ p1))) ∨ p1) ∨ (((True ∧ ((p3 → p5) ∧ p5)) → True) ∧ p4)) ∧ p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149796578499675521789854368459 : ((False ∨ ((p1 ∨ p2) ∨ (((p3 ∨ (p2 ∧ p1)) → ((((p5 ∧ True) ∧ p1) ∨ (False → True)) ∨ p2)) ∧ True))) ∨ (p3 ∨ (p3 → (p1 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788933427846615599512776695912 : (((p5 ∨ (((p2 → (((p1 → p5) ∨ p4) ∨ ((((True ∨ ((p3 → p4) ∧ p2)) ∨ p2) ∧ (p4 ∧ p2)) ∧ p3))) → p3) ∨ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618809549668145711485525869639 : (((((p3 ∧ (p4 ∨ p4)) ∧ ((p3 ∧ (p2 ∨ ((((p5 ∨ p2) ∨ p5) → (p5 → (True ∧ ((p5 ∧ True) ∧ p3)))) ∧ p2))) ∨ p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690668179702267640544891387370 : (((((p1 ∧ (((((p1 ∧ ((p5 ∨ p1) ∨ p5)) ∧ p2) ∨ p4) ∧ p2) ∨ p1)) ∨ p2) → ((p1 → (True ∧ False)) ∨ ((True → True) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149660490532990305284999008465 : ((p4 ∧ (p2 ∧ ((p3 ∧ (p4 ∨ (((((p5 ∨ True) → ((p4 ∧ False) ∧ True)) ∨ False) ∧ p4) → False))) → p4))) ∨ (((False ∧ p4) → p4) ∨ p3)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340182923962358950315247213625 : (p1 → (p4 → ((p2 ∧ False) ∨ (((p1 → ((p2 ∧ (False → ((False ∨ p5) → p2))) → (p3 ∧ p4))) → p2) ∨ (p3 → ((p3 ∧ p1) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



