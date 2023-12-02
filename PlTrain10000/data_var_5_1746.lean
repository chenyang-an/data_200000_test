variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42345939048678568035686577922 : (((p3 ∧ (((p4 ∨ (p5 ∨ (p3 → ((False ∧ True) → ((True ∧ p2) ∨ p1))))) → p2) ∨ ((False ∧ (p4 → (True → p4))) ∨ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304279924297025015968993296386 : (p1 ∨ (((p2 → ((p3 ∧ p4) ∨ (((True ∧ ((p5 → (p1 ∧ True)) ∨ p1)) ∧ p1) ∨ (False ∨ (False ∨ (p5 ∨ True)))))) → (False ∧ True)) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p3 ∧ p4) ∨ (((True ∧ ((p5 → (p1 ∧ True)) ∨ p1)) ∧ p1) ∨ (False ∨ (False ∨ (p5 ∨ True)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637228631276322350026250323688 : ((((((p5 → (p1 ∧ (((p5 ∨ (True → p2)) ∧ p1) ∧ False))) ∧ True) → (((p2 → ((True ∧ (p3 ∧ p1)) ∨ p5)) ∨ p1) ∨ False)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338066180192458565698386923564 : (p1 → (((False ∨ (True ∧ (p2 ∧ (False → p5)))) ∧ (p3 → p2)) → ((False ∨ (p3 ∨ False)) ∨ ((p5 ∨ ((p3 → (True → p3)) ∨ p4)) ∧ p1)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57966718749517613848127787241 : (((p2 → (p5 → False)) → (((p5 → p5) ∧ ((p2 ∨ (p5 ∨ p2)) ∨ p4)) → ((True ∧ ((p4 → False) ∨ (p1 → p5))) ∨ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313317475821352135142565822518 : (p3 ∨ ((p2 ∨ ((p1 ∨ p1) → (((((p4 ∧ True) ∨ (False ∨ p3)) → ((p1 ∨ p2) → True)) → ((p3 ∨ p3) ∨ p4)) ∧ (p1 ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314740561157135440047164362720 : (p3 ∨ ((((p1 → (p4 ∨ False)) → (p2 → ((p4 → (True → True)) ∧ p2))) → p3) ∨ (p3 → (p2 ∨ ((p4 → False) → (True → (p2 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119287445273712423710247635329 : ((p3 → (((p3 → False) ∨ (((p4 ∧ False) ∨ (((p2 ∧ p1) → ((p1 → p5) ∨ (p4 ∧ p1))) ∧ (p2 → p1))) → p2)) ∨ p3)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256479883801232907329072849518 : ((False ∨ p4) → ((((p1 ∧ True) ∧ False) ∧ ((p5 ∧ p1) ∨ (p4 → False))) ∨ (p3 → (((((p3 → True) ∨ p4) ∨ p5) ∧ (p1 ∨ p1)) → p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326157691047508084116181210519 : (p5 ∨ (p2 → (((((p4 ∧ p5) ∨ ((((((False ∨ False) ∧ ((p3 → True) ∨ p5)) ∨ p5) ∧ p4) → p2) ∧ False)) ∨ (p3 ∧ p2)) ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655201107392867466230810355751 : ((((((((p2 → p2) ∧ (((True → p2) ∧ (((p3 → p5) ∧ False) → p2)) ∧ p1)) ∧ (False ∧ p5)) ∨ p5) ∧ (p2 ∨ p1)) ∨ (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262151053326081523336174910358 : (True ∧ ((((((p2 → ((True → p4) ∨ (p5 → (p1 → p4)))) ∧ (True ∨ p3)) ∧ ((p5 → p1) ∨ p5)) ∨ ((p3 ∨ p3) ∧ p2)) ∨ True) ∨ p1)) := by
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
theorem thm_5_vars_785183433276524512218599016189 : (((p4 ∨ ((((p1 ∨ ((True ∨ p5) → p2)) → False) ∨ (False ∨ ((False → p2) → ((p2 → p4) → ((p5 → p1) → (p2 → p3)))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685991868592253725459719454147 : (((((((False ∨ ((p2 ∨ p3) → p4)) → p2) ∧ ((False ∨ p1) ∨ (True ∨ p1))) ∨ (False ∧ False)) → (p4 ∨ ((p5 ∧ p3) ∧ (True → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52171633412489399597416544623 : (((((((p1 → p3) ∨ True) → p1) ∨ True) ∧ ((p1 → p3) ∧ ((p5 ∨ p4) → True))) → ((p5 ∧ (p1 ∧ (p5 → (False ∧ True)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184071009127081282984445648784 : ((((False ∨ ((p2 ∨ p1) ∨ p3)) ∧ ((False ∨ p1) ∧ True)) ∨ False) ∨ (False → (((p1 ∧ False) ∧ (p3 → p4)) ∨ ((p4 → (p2 → True)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227516421150238321757471441103 : ((True ∧ (p3 ∨ p4)) ∨ ((((p1 ∧ ((((((p5 → p3) ∧ p3) → (p2 → False)) ∨ p1) ∨ p5) ∧ p1)) ∨ (p4 ∨ True)) ∨ (p1 ∧ False)) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146381983245686008094794165489 : ((p1 ∨ (p5 ∨ (((((p2 ∨ False) ∧ ((p5 → p3) → (p2 ∧ (p3 ∨ True)))) ∨ (True ∨ p4)) → False) → p5))) ∧ (p3 → ((p5 ∧ p4) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ False) ∧ ((p5 → p3) → (p2 ∧ (p3 ∨ True)))) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112707746694017827691924362397 : ((((True ∧ (((p2 ∧ p3) → p5) ∨ (p2 → (((p4 ∨ p4) ∨ False) ∨ (p5 ∨ True))))) → (False ∨ ((p1 ∨ p5) ∨ p2))) → p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231869064198189933822755840180 : (((True ∨ False) → p4) → (((True → (p3 ∧ p1)) ∧ (True ∨ p5)) → (p2 → (p1 ∧ (True ∧ ((p2 ∨ False) ∧ ((False ∨ (True ∨ p3)) ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113539148730227076206689997517 : ((((((p1 ∧ p2) → p3) → False) ∨ ((p5 ∧ p2) ∧ ((False → p2) ∧ (p5 ∨ (p4 → ((False ∧ False) ∧ False)))))) ∨ (p3 ∨ True)) ∨ (p4 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158476778981718316792328161283 : (((p5 → p3) ∨ ((True ∧ p5) ∧ (((p1 → ((p4 → False) ∨ False)) ∨ ((p1 ∧ False) → p1)) → p4))) ∨ ((True → False) → (p4 ∧ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190450470289605782052153517072 : (((p3 → ((p4 ∨ ((p2 ∨ p3) ∧ p2)) → p4)) ∨ p5) ∨ (((True → False) ∧ (p2 → (p3 ∧ ((False ∨ ((p1 ∨ True) ∧ p2)) ∨ True)))) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62567373649121969002189569174 : ((p3 ∧ (True → ((((True ∨ True) → (True → (p3 ∨ (p1 ∧ (((p1 → p2) ∨ ((p5 ∧ p1) ∧ p5)) ∨ p4))))) ∧ (False → p2)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49288907149278314025919168981 : (((p5 ∧ ((((False ∧ p4) ∨ p5) → False) → ((p2 ∨ p5) ∨ (((p4 ∨ True) → p4) ∧ ((True → p5) ∨ p3))))) ∨ ((False → p5) ∧ True)) ∨ p5) := by
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
theorem thm_5_vars_178307772507659467374757709386 : ((((p5 ∨ ((((p5 ∨ False) ∨ p3) ∨ False) ∨ p3)) ∧ p1) ∨ (p5 ∨ True)) ∨ (p1 ∨ ((p4 ∧ ((p4 ∧ p3) ∧ p5)) → (p5 ∨ (True ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58123366102150996926352471615 : (((p2 ∧ True) ∧ (p5 ∨ (p2 ∨ ((p1 ∨ (((p3 ∧ p3) ∧ (p3 → p3)) ∨ (((p4 → False) → ((False ∧ False) ∧ p3)) → False))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18104293248132824118868981940 : (((True → ((((True ∨ (((((p1 ∧ p2) ∨ p2) → p5) ∧ p4) ∨ p2)) → p3) → (p3 ∧ False)) → False)) ∨ (True ∨ ((False ∨ p1) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754806799626531903554324134463 : (((False ∧ (p1 ∨ (((((p1 → True) ∧ p5) ∨ ((((p3 → (p1 → p2)) → p5) ∨ (False → p1)) ∧ (True ∧ (p1 ∨ p2)))) ∨ False) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319622028768510095613949196384 : (p4 ∨ ((p5 ∨ ((((p3 ∧ p4) → p2) → p3) ∨ True)) ∧ (p4 → (p4 ∨ (p5 ∧ (True ∧ ((p4 ∧ (p2 ∧ ((p5 ∨ p1) ∨ True))) ∨ p3))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789230316773861023257355239395 : (((p5 ∨ ((((p5 ∨ p5) → (((p2 ∧ p3) ∨ (((p5 ∨ False) ∨ p3) ∧ p4)) → (True → p2))) ∧ p4) ∨ ((p5 ∧ (p5 ∨ p3)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346386153013832458925309893196 : (p3 → ((p5 ∨ (((((p5 → p5) → p5) ∧ (p2 → (p4 ∧ p1))) ∨ False) → (((False ∨ ((p4 → p1) ∨ p4)) ∧ False) ∨ True))) ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694749573381699335433022561528 : ((((p4 ∨ ((False ∨ (False ∨ (p5 ∨ (p2 → p1)))) ∨ ((False ∨ True) ∨ True))) ∨ (p4 → (True ∧ ((p4 ∧ p2) ∨ ((True → p5) ∨ p5))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709699611528120838141533245243 : ((((p5 ∨ (False ∨ ((False → p5) ∧ (p3 → True)))) → (False ∧ (((False → (p5 ∧ (p4 ∧ False))) ∧ p1) → ((False ∨ p5) ∨ (p2 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624675892852709435444446106948 : ((((p4 ∨ (p2 ∧ (((p5 ∧ ((p1 ∧ ((p2 ∨ p4) ∧ (p5 → (True ∧ ((p5 → p3) → p4))))) ∧ (p3 ∧ p1))) → p1) → p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111710166816610411379136037591 : (((((((False ∨ ((((False → False) ∧ (p5 ∨ True)) → True) ∧ True)) ∨ False) ∧ p4) → ((p1 → (p5 → p4)) ∨ False)) → p4) ∨ True) ∨ (p1 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322567109886789845688483860218 : (p5 ∨ ((p3 ∨ (((True ∨ (p2 ∨ (p1 → ((p2 ∧ p3) ∨ (((p2 ∧ True) ∨ ((p3 → p2) ∧ p1)) ∧ p2))))) ∧ True) → (p1 ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42724399063421954277377050422 : (((True → (((p5 ∨ p2) ∨ ((p2 ∨ ((True ∨ ((False → False) ∧ p1)) → ((p2 → (p1 ∨ p5)) ∨ (True ∨ p5)))) ∧ p4)) ∧ p2)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40399434258214588217743203021 : (((((p4 ∧ ((p5 ∧ p4) ∧ ((((p3 ∨ (p5 ∧ (p5 ∨ (p4 → True)))) ∨ True) ∨ p1) ∧ p5))) ∧ (False ∧ (p3 ∧ p2))) ∨ True) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66554497349191158387208989301 : ((True → (((((((True ∨ p2) → True) → (p1 ∧ False)) → (p5 ∧ False)) ∨ False) ∧ ((p3 ∧ p1) → (False ∨ (p1 ∨ False)))) ∧ (p5 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2369116195624179873832559513 : (((p4 ∧ ((p5 → (False ∨ p2)) → (p2 ∨ p2))) ∨ (p1 ∧ True)) ∨ (((False ∨ p4) ∧ (True ∧ ((p5 ∨ (True ∨ p4)) → p1))) → p4)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157386197975644008129151099981 : (((((p2 ∧ (((p4 ∨ p3) ∨ ((p3 ∧ True) → True)) ∧ p5)) ∧ (False ∨ p1)) ∨ p3) ∧ (False → True)) ∨ (True ∨ ((p4 ∧ False) ∧ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212173606175203687535233940640 : ((True ∨ ((p3 → p2) → p3)) ∧ (((p2 ∧ (True → (((p3 ∧ p1) ∨ False) ∨ (((p2 ∧ False) ∧ False) ∨ False)))) ∨ (True ∨ (p1 ∨ p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19686803686379300869422320604 : (((p1 → ((p5 ∧ (p4 ∨ p2)) → (((p3 ∨ True) ∨ (p5 ∨ (p2 ∧ p5))) → p4))) ∨ (((p3 → p1) ∨ (p4 ∧ (p1 → p3))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_183966638174738166683388168989 : (((p2 → (((p2 ∧ True) → True) ∧ ((p5 ∨ p4) ∨ p1))) ∧ False) ∨ (False ∨ (True → ((False ∧ (False ∧ (p4 ∧ p2))) → (p2 ∨ (p1 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_42217994512052165449537233405 : (((False ∧ ((((False ∨ ((True ∧ ((True → True) → (((p5 → p4) → (p3 ∨ False)) → p3))) ∨ p3)) ∧ (p4 → p2)) ∨ False) → p5)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112279053093124789883522379809 : (((True → ((p2 ∨ True) ∧ ((((p2 ∨ p1) → p3) ∨ ((((p1 ∨ (p2 ∧ p5)) ∨ False) → p5) → p4)) ∨ (True ∨ p4)))) ∨ p2) ∨ (p4 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262506700702191692437200749033 : (True ∧ ((p3 → (((((p3 ∧ (p2 → (p1 → ((((True → (p2 ∨ True)) → p5) ∧ p2) → p4)))) ∨ p5) → p4) ∧ False) ∨ (True → p3))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313971563168060427799085505956 : (p3 ∨ (((((p4 ∧ (p5 ∨ (True ∨ False))) ∨ (True ∧ (True ∨ p2))) ∧ (p3 ∨ False)) ∨ (True ∨ (((p5 ∧ True) ∧ p2) → p5))) ∨ (p5 ∨ p2))) := by
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
theorem thm_5_vars_98820193219142722701842789282 : ((True → (((False ∧ False) → (False ∨ (False → ((p3 ∨ ((True ∧ (p1 ∧ True)) → ((((p3 ∨ p4) ∧ p1) → p4) ∧ p1))) → p1)))) ∧ False)) → p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41648947989004041686766896214 : ((((((True → p5) → p4) ∧ (p1 ∨ True)) ∧ ((((p1 ∨ p4) ∧ p3) ∧ p5) ∨ (((False → p5) → p1) ∨ (False → (p1 ∧ p1))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178121113828901273372014656171 : ((((p5 ∨ (p1 → ((p4 ∧ p1) → p4))) ∧ ((p2 → p1) → True)) → p1) ∨ (True ∨ ((p1 → ((p2 → ((p5 ∧ p4) → p5)) ∨ p5)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111071301165553457319890004874 : ((((True → ((False ∨ p1) ∧ (False ∨ (True ∨ (p2 ∨ (p3 → (p3 → p2))))))) ∨ (((p3 ∨ p5) ∨ (p4 → True)) → p5)) ∧ False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55111436170940624572388310602 : ((((((p4 ∧ p3) ∧ False) ∨ p1) ∧ p4) ∨ (True → ((((((False ∧ p1) ∧ p1) ∧ p4) ∧ p2) → (p1 ∨ (p2 → (True → True)))) → True))) ∨ p1) := by
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
theorem thm_5_vars_52802749134827315091172170305 : (((((p4 → p4) → (False → ((p5 ∨ False) ∨ p3))) → (p4 ∨ (True ∧ p2))) → (p1 ∧ ((p4 ∨ (p5 ∨ ((p3 → p5) ∨ False))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40733967632439331555852392810 : (((((((p5 ∨ p1) ∨ p4) ∧ p1) → (((p5 → ((p4 ∨ (True ∧ False)) ∧ p2)) ∨ (p2 ∨ False)) ∧ (p4 → (False ∨ p3)))) → p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54921427048013940180999659084 : (((((p4 ∨ False) ∧ (p1 → False)) → True) ∧ (((p2 ∧ (p3 → p4)) ∨ p3) ∨ ((False ∨ ((True → p3) → (False ∧ (p1 ∨ False)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148594412442420399204770974849 : ((((p2 ∨ False) ∨ (p3 ∨ ((p5 ∨ p1) ∨ (p1 ∨ False)))) ∨ ((True ∨ ((p4 → (p5 ∧ p3)) ∨ p5)) ∨ True)) ∨ (p4 ∧ (p2 ∧ (p3 → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349310849307281750429063255644 : (p3 → (p2 → (True ∧ (((((p1 ∨ ((False ∨ p1) ∨ p4)) ∧ p4) ∨ True) ∨ (p5 ∧ p3)) ∨ ((False ∨ ((p4 → (p5 ∨ p1)) → False)) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_206381044706340516572256481701 : ((p2 ∨ (p5 → ((True → p3) → p4))) ∨ ((p3 ∨ (p3 → (p3 ∧ p4))) ∨ (p1 ∨ ((p3 ∨ (p2 ∨ ((True ∨ False) → (p1 → p3)))) ∨ True)))) := by
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
theorem thm_5_vars_50037857430995418865625964303 : (((((p4 ∧ p4) ∧ p2) ∨ ((((False → p4) → True) → (p5 → p4)) ∧ ((p3 ∨ (False ∧ True)) ∨ p4))) ∧ ((p3 ∧ (True ∧ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585711477238296564949961209140 : (((((((((p1 → p5) ∧ ((p1 ∨ p2) ∨ ((True → p5) ∨ p4))) ∧ (p3 ∨ (p4 ∨ False))) ∧ ((p5 ∨ p5) ∧ True)) → p3) ∧ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51312659128761044358245888268 : (((p3 ∨ (p1 ∧ ((((p4 ∨ (True → p3)) ∨ (p3 ∧ (p1 ∧ p3))) → (p4 ∧ p5)) ∧ p4))) ∨ (False ∨ ((p5 ∧ (p1 ∧ p4)) → p4))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957941003054838483298745095332 : ((((p5 ∨ (p2 → p2)) → (((((p1 ∧ ((p3 ∧ (True → p3)) → p1)) ∨ (True ∧ (p5 ∨ (p3 → p1)))) ∧ p4) → (p4 → p3)) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p2 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18105190425598282910350461252 : (((True → (((p2 ∧ ((p1 → p1) → (p1 ∨ (p2 ∧ p4)))) → p4) ∧ ((p3 → (p2 ∨ p5)) ∨ p5))) ∨ (p3 ∨ ((p3 ∨ True) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_915052740680693864003039349561 : ((((False ∨ ((((p5 → p3) → ((True ∨ p3) → ((p3 → True) ∨ True))) → True) → False)) ∧ (p4 → (p4 ∨ (((False ∧ p2) ∨ p3) → p5)))) → p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p5 → p3) → ((True ∨ p3) → ((p3 → True) ∨ True))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42380465071243575210284416619 : (((p4 ∧ ((False ∧ ((False ∨ (p1 ∧ p1)) ∧ ((True ∧ (p4 → (p3 → (p3 ∧ (True ∧ p1))))) ∨ (p4 ∧ p5)))) ∨ (False → p5))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246633726565811708897949469259 : ((p5 ∧ p3) ∨ (((p4 ∨ p4) ∧ ((False → (True ∨ ((True ∧ ((True ∨ False) ∧ (p5 → (p5 → p3)))) → p4))) ∧ p5)) ∨ ((True ∨ p5) ∧ True))) := by
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
theorem thm_5_vars_712387653845195706121020266206 : ((((((False ∨ p2) ∨ False) ∧ (False ∨ p4)) ∨ ((p5 → ((p1 ∧ (((p4 ∨ p4) ∨ p4) ∧ p3)) ∧ True)) ∨ (True ∧ ((p2 ∧ p5) → p2)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_179096946766018919281023661465 : ((False ∧ ((p1 ∧ ((True ∨ (p2 ∨ False)) ∧ (False ∨ p3))) ∧ (True → p1))) ∨ (((p5 ∧ p2) → (True ∧ ((p2 ∨ p3) ∨ (True ∧ False)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171897169668311782344926582381 : (((p4 ∨ ((p3 ∧ p5) ∧ (((p2 ∨ ((True → p2) ∨ p5)) → p3) ∧ p4))) → p2) ∨ ((p2 ∧ p1) → ((p5 → p1) ∨ (p5 ∨ (p2 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672874698436452020642148984073 : ((((((p2 ∨ p5) ∧ (p4 ∨ ((p5 ∧ ((p5 → False) ∧ (p4 → p2))) ∨ (p3 ∧ p1)))) ∨ ((p1 ∧ False) → p5)) → (p1 ∧ (True ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56501634702488839184754536090 : (((p2 ∧ ((p2 ∧ p3) → p2)) → ((False ∨ (p2 ∨ p2)) → ((p2 → p3) ∨ ((True → False) → (p4 ∧ ((p4 → (p1 ∨ p1)) ∨ p3)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
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
      let h14 := h1.left
      let h15 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47775684095948203803072622062 : ((((p1 → ((p3 → ((p3 ∧ p5) ∨ (((p5 → (p5 ∧ p5)) ∨ p2) ∨ (p3 ∧ ((p5 → p2) ∧ p5))))) ∨ True)) ∨ False) → (p1 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316883316378390635454150508575 : (p3 ∨ (p1 → ((p2 ∧ (p5 ∨ p3)) → (((((p2 ∧ p2) ∧ (p1 ∧ (p1 ∨ p2))) ∨ p5) ∧ (p4 ∧ ((p5 ∨ (p1 ∧ False)) ∧ p1))) ∨ True)))) := by
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
  cases h4
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
theorem thm_5_vars_65584744270314116425635263612 : ((p4 ∨ (((p1 → (True ∧ ((((p4 ∧ p5) ∧ (True ∧ p5)) ∨ ((((False → p3) ∨ p5) ∨ (True ∧ p1)) ∨ p5)) ∨ p4))) ∧ p4) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41136927646732791843103770832 : (((((p2 → ((p1 → ((((False ∨ (p2 ∧ False)) ∨ p5) ∨ p1) ∨ False)) ∧ (p5 → p1))) ∧ (p1 ∧ False)) ∨ ((p1 ∧ p4) ∨ p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178670694506263847817626708236 : (((p2 ∧ ((p3 ∨ p1) → p4)) ∧ ((((p2 ∧ p3) → p5) ∨ True) → p2)) ∨ ((((p5 → False) ∨ True) ∨ ((p1 → p1) ∧ (p3 ∧ p3))) ∨ False)) := by
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
theorem thm_5_vars_337993890239012711451150676210 : (p1 → ((p1 → ((p4 ∨ (p2 → True)) → (((False ∧ p3) ∧ p3) ∧ p1))) → ((p2 ∧ (p5 ∧ (p3 ∧ ((p1 ∨ (False → p4)) → False)))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : (p4 ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h13
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- False on the left can always be used.
  apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h19 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h20 := h2 h19
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h21 : (p4 ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h23 := h20 h21
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- We need to get the right conjuct of h24 based on <expert-advice>.
  let h25 := h24.right
  -- One of the premise coincides with the conclusion.
  exact h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h28 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h29 := h2 h28
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : (p4 ∨ (p2 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h32 := h29 h30
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- False on the left can always be used.
    apply False.elim h35
  case inr h36 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h37 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h38 := h2 h37
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h39 : (p4 ∨ (p2 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h40
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h41 := h38 h39
    -- We need to get the left conjuct of h41 based on <expert-advice>.
    let h42 := h41.left
    -- We need to get the left conjuct of h42 based on <expert-advice>.
    let h43 := h42.left
    -- We need to get the left conjuct of h43 based on <expert-advice>.
    let h44 := h43.left
    -- False on the left can always be used.
    apply False.elim h44
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172296345204136815432661520588 : ((((((True ∨ (p3 → p1)) ∨ p4) ∧ p1) → p2) → ((p5 → (p5 ∨ p4)) → p2)) ∨ (((((p2 ∧ p3) ∧ (p2 ∧ p2)) → p3) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16661059527774103209869098564 : (((((((((p1 → ((p5 → p1) ∨ p3)) ∧ False) ∧ p1) ∧ True) ∨ p4) → ((p3 → (True ∨ False)) → p2)) → p2) ∨ ((False ∨ False) → True)) ∧ True) := by
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
theorem thm_5_vars_160436239574449975021728721226 : (((False → ((p1 ∨ ((p2 ∨ True) ∨ ((p1 → (False ∧ p4)) ∧ p1))) → True)) ∨ ((p5 ∨ p2) ∧ True)) → (p4 → ((p5 ∧ (True ∧ p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157631457828162500407565280874 : ((((p4 ∨ False) ∧ (((p4 → ((p3 ∨ p2) ∨ p2)) → (p1 → False)) → p4)) ∧ ((False → p5) ∧ p4)) ∨ (True ∨ ((True → p5) ∧ (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801154178828698495957717532783 : (((p2 → ((False ∧ (p4 ∨ (((False → ((p4 ∧ ((False → (p4 ∨ False)) → p1)) → False)) ∧ p1) ∧ p5))) ∨ ((p1 ∨ (p3 ∧ p5)) ∨ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303044023584858191160008852004 : (False ∨ (p2 → (((p5 ∨ (p2 ∨ ((((((p1 ∨ (p1 ∨ p5)) ∨ False) → p5) ∨ p5) ∧ True) → (True → p5)))) → ((p3 ∧ p4) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247634222732077858049012043775 : ((False ∨ p5) ∨ (p1 ∨ (p4 → (False ∨ (((False ∧ True) ∨ (p5 ∧ (p4 ∨ (p2 → (p4 ∧ (True → p3)))))) ∨ (p2 ∨ ((p4 → p1) ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_661885851081792205867576016047 : (((((((p3 ∨ True) → (p1 → (((p5 ∧ (p1 → p3)) ∨ p3) ∨ p2))) ∨ p4) ∧ ((p2 → ((False ∨ True) → p3)) ∧ p1)) → (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158621987289271514724754661450 : ((False ∧ (False ∨ (((True → (p5 → (p3 ∧ False))) ∧ (p3 ∨ (False ∨ (p2 ∧ p2)))) → (p5 → p1)))) ∨ ((p1 → p1) ∧ (p1 → (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172632843247546533770780872465 : (((p4 ∧ p4) ∧ ((p4 ∨ (True → p5)) ∨ ((p1 → p3) ∨ (p1 ∧ (p3 ∧ False))))) ∨ (((p5 → p5) ∨ ((True ∨ (False → p1)) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302654463143330903547260118858 : (False ∨ (p2 ∨ ((False → p1) → ((((((p5 → True) ∧ ((False → (p5 ∨ True)) → p3)) ∧ p3) ∨ (p2 → p4)) ∨ True) ∧ (p2 → (p2 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356382845404308921350766889814 : (p5 → (((((p1 → p3) → p1) ∧ ((p3 → p4) ∨ False)) ∨ ((p2 ∧ True) → p4)) → ((True ∧ ((p5 → ((p2 ∧ p1) ∧ p1)) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43925260046706014967756580395 : ((((((((p2 ∨ ((p2 ∨ (p1 ∧ (True → p4))) ∨ ((p3 ∧ p3) → False))) ∧ p4) ∧ p5) ∨ p5) ∨ (True ∧ False)) ∨ (p5 → p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51277140409959880036880923755 : (((False ∧ (p4 ∨ (p3 ∨ (((p2 ∧ (True ∨ (p3 ∧ (True → (False ∧ p1))))) ∧ p5) ∧ True)))) ∨ (False → (((True ∨ p4) → p1) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135791361935894091476441139233 : (((((True ∧ True) ∨ True) ∧ (((p3 ∨ False) ∨ p4) → ((p3 → p4) → p3))) → ((((p1 → p3) → False) ∨ p1) ∨ False)) ∨ (True ∨ (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193973330618618666263828664146 : ((p3 ∨ (((((p5 ∧ p3) → p2) ∨ False) ∨ True) → True)) → ((p1 ∨ (((p1 ∨ p1) ∨ p4) → ((False ∨ ((p2 ∧ p4) ∨ True)) ∨ p2))) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135868494463165663570874080400 : ((((p2 → (p1 ∨ (False ∧ (p5 ∨ p3)))) ∧ ((True → p2) ∨ p1)) ∨ ((False → True) ∨ (((p1 ∧ p4) → p2) → True))) ∨ ((p4 ∧ False) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254695107767511631264310332322 : ((p3 ∧ p3) → (((((p5 → ((p5 ∧ ((p3 ∨ p1) → (p1 → (False → (p2 ∨ True))))) ∧ True)) ∧ p5) ∨ (False ∨ False)) ∨ (p5 ∨ p1)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634773221997731057372322173206 : ((((((p2 ∧ (((p1 ∨ p1) ∨ (((p4 ∨ True) ∧ p5) ∨ p4)) ∧ (p1 → p3))) ∧ (True → (False → True))) ∨ ((False → p5) ∧ p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157008116857077458160965768011 : (((((False ∨ p1) ∧ p4) ∨ ((p5 ∧ (p1 → p4)) → ((False ∨ (p1 ∧ p3)) ∧ (p4 → True)))) ∨ True) ∨ ((p4 → p4) ∧ ((p1 ∧ p3) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50111802832348105088019614499 : (((False ∨ (((p1 ∨ ((p1 ∨ (True ∧ (True ∧ ((p5 ∨ (p4 ∧ p2)) ∨ p3)))) → p4)) ∨ False) → p2)) ∧ ((p3 ∨ p3) ∧ (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



