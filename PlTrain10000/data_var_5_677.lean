variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156886091540094587312681871349 : ((((((p3 ∨ ((p1 ∧ (p1 ∧ p1)) → True)) ∧ ((p5 ∧ p4) ∧ False)) ∧ (p5 ∧ p4)) ∨ p3) ∨ True) ∨ (p5 ∨ (((p3 ∨ True) ∨ False) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299241746326517782535222244434 : (False ∨ ((((p1 ∧ (True ∧ ((p5 ∧ p1) ∨ False))) ∧ (p1 ∨ (((p1 ∧ (True ∧ True)) ∧ True) ∨ (p1 ∨ p2)))) ∨ ((p5 ∨ p1) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43741811010094210686895747787 : (((((p5 ∧ p1) → (((p3 → ((p3 ∧ True) → p4)) → ((p1 ∧ p4) ∨ p2)) ∨ (((p5 ∨ False) → p2) ∨ (False → p1)))) → False) → False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ p1) → (((p3 → ((p3 ∧ True) → p4)) → ((p1 ∧ p4) ∨ p2)) ∨ (((p5 ∨ False) → p2) ∨ (False → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58301685741451381803020601238 : (((True ∨ p3) ∧ (((p5 ∧ p5) → p4) ∨ (((((p1 → (p2 ∧ ((p2 → (p1 ∨ (p3 ∨ p5))) → p4))) → False) ∧ False) ∧ p1) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53086209663524824020863379387 : (((False ∨ (((p3 ∨ False) ∨ (p5 ∨ (p5 ∧ p1))) ∧ (p1 ∨ p4))) ∧ ((p5 ∧ ((p4 → True) ∧ p4)) ∧ (((False ∨ p5) ∧ False) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42008009017453662175803525536 : ((((p3 → p3) ∧ (p1 ∧ (True → (((p2 ∧ True) ∧ (p2 → (p3 ∨ (p5 → p3)))) ∧ (False → ((False ∧ p2) → (False ∧ True))))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59007292989271240892497589869 : (((p3 ∧ p3) ∨ (((False ∧ (False ∨ (True ∨ ((((True ∧ p4) ∨ (p3 ∧ p1)) ∧ (p1 ∨ p3)) ∧ ((p5 ∧ True) ∧ p3))))) ∧ p2) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184593875763734236301657811905 : (((p1 → (p3 ∧ (((p1 ∨ p5) → p4) ∧ True))) → (p1 → p2)) ∨ ((((True → p3) ∧ p5) → p3) → (p3 ∨ ((False ∧ (p2 → False)) → p3)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215799061714469026211527660165 : ((p1 ∨ (p4 ∨ (p2 → False))) ∨ ((p3 ∨ ((p4 → ((p1 ∧ p2) ∧ (p4 ∨ (p4 ∨ (False ∨ p5))))) ∨ ((True ∨ (p3 → p2)) ∧ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159617568960699123072538378575 : (((((p4 ∧ p4) → (((False ∨ p2) ∧ (((p1 → p2) ∧ False) ∧ (p3 → p4))) ∨ True)) ∧ True) ∨ False) → ((False → p5) → (p5 → (p3 ∨ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798660245689856144612835478920 : (((p1 → ((((p4 ∧ False) ∧ p3) ∧ p1) ∨ (p5 ∧ (((False ∧ p3) → ((p5 ∨ ((True ∧ True) ∧ (p1 ∧ p3))) → True)) ∨ (p4 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234229063325725364570128944482 : ((False → (False ∨ p2)) → ((((((p4 → p1) ∨ p4) ∨ p3) ∧ (p2 ∨ (False → ((p2 ∧ False) → p3)))) ∨ p1) → (p2 ∨ (p1 ∨ (p1 → True))))) := by
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
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678342818528009857380322000746 : (((((p1 ∨ (True ∧ (p5 → (p5 ∨ True)))) ∧ (((False → p2) ∨ p4) → ((p5 → (True → p1)) ∧ p4))) ∨ ((p3 → p3) ∧ (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614311494406369943104006259146 : (((((((p3 → True) ∨ p3) ∧ ((((((p1 ∨ (p2 ∨ p3)) ∨ (p1 ∨ p4)) → p1) → p5) ∧ p3) → p3)) → (p3 → (p5 ∨ False))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196851184300968027297373657977 : (((False ∨ ((p5 ∧ p4) → (p3 → p5))) ∧ p5) ∨ (p1 → ((p2 ∧ p5) ∨ ((True ∧ (p2 → ((p4 ∨ ((p1 ∧ p4) ∨ p1)) ∨ True))) ∨ p1)))) := by
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
theorem thm_5_vars_345402162548238963538147848612 : (p3 → ((((p5 ∧ ((p1 ∨ ((True → (False → (((True ∨ True) ∧ p1) ∧ (p2 → p2)))) ∨ p4)) ∧ (p3 → False))) ∧ (False → True)) → p2) ∨ p1)) := by
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
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h17
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190753504277720864834684562241 : (((p5 ∨ (True ∧ (p1 ∧ (False ∨ p4)))) ∧ (p1 ∧ False)) ∨ (p2 ∨ (p4 ∨ (p3 → (True ∨ ((p5 → ((p5 ∨ p4) ∨ False)) → (p2 ∨ p1))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598131004703384894959411757465 : ((((((p5 ∨ p2) ∧ False) ∨ ((p2 → (((p1 ∧ p3) ∧ True) ∨ ((((False ∧ (p1 → p2)) ∧ p3) ∨ (p5 → p2)) → False))) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173801582788930207195417023311 : (((p2 ∧ (((False ∨ True) ∧ (p4 ∨ ((p1 → False) ∧ p4))) ∧ (True → True))) ∨ p4) → (((False ∧ ((p4 ∨ p2) ∧ (p2 → p3))) ∧ p1) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627579963215383877409519609185 : ((((((p2 ∨ (((p1 ∧ (p3 ∧ (p1 ∨ ((p3 → p1) → (p2 ∧ p3))))) → p4) → ((False ∨ p5) → p1))) ∨ (p5 → p2)) ∧ p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130893780479052574407969740755 : ((((((True → (p5 → False)) ∧ p1) → (False ∧ (p3 ∨ False))) ∧ p5) ∨ (p2 ∨ (((False ∧ p5) ∧ (p3 ∨ p1)) → p4))) ∧ (p4 ∨ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618071556097426590560749879706 : ((((((True ∧ p3) ∨ (p3 ∨ p3)) ∧ ((((p1 → p2) ∧ True) ∨ False) → (False ∧ (p2 ∧ (p4 ∧ (((p5 ∨ p4) ∨ False) → True)))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134271084510663625964763674693 : ((((p4 ∧ p5) ∧ (((p5 ∧ True) → p2) ∧ ((True ∧ (p5 ∨ False)) ∨ ((((False ∧ p2) ∨ False) ∧ p5) → True)))) ∨ p3) ∨ ((True → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165220255186782763209871493572 : (((((((False ∧ True) ∨ False) ∧ p5) ∧ p2) ∨ (p4 ∨ (p2 ∧ (p5 ∧ p4)))) ∨ (p4 → True)) ∨ ((((p5 ∧ p1) ∧ p3) ∨ (p3 → p1)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46589468016598430976856767579 : (((False ∧ (True → (p2 ∨ ((p3 ∨ (False ∧ p1)) ∨ (p5 → ((True ∧ ((p1 ∨ False) ∧ (p2 ∨ p4))) → (p4 ∧ p3))))))) ∧ (False ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732892388502616149827801545078 : ((((p2 ∧ p1) ∧ ((((p3 ∨ p2) ∨ False) ∨ p5) ∧ (p1 → ((True → (p1 → p5)) ∨ ((((p1 ∧ p5) → (False → p3)) ∧ p3) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626853103894589571760311277825 : ((((p5 → ((p3 → p5) ∧ ((p3 ∨ (p5 → False)) → ((p1 ∨ ((((p4 ∨ p5) → ((p2 ∨ p4) ∧ p5)) ∨ False) → p4)) ∧ True)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962633226654418255958083248893 : ((((False → True) ∧ (((True → p5) ∧ (p3 ∧ (((p1 → p2) ∨ p5) → ((p2 ∨ p4) → ((((p3 → p4) → True) → p3) ∧ p5))))) ∨ False)) → p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341709337549057110346506420894 : (p2 → (((p1 ∨ (((p3 ∧ (False ∧ p5)) ∧ (p5 → True)) ∧ ((True ∧ p5) → p2))) ∧ (p2 → (((p2 ∨ True) ∨ p4) → p2))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310980383354773291683245911013 : (p2 ∨ ((False → True) ∧ ((p3 ∨ ((p5 ∨ p3) ∨ p3)) ∨ ((p1 → (((((p2 → (p4 → p3)) ∧ p4) → p4) → p3) → (False ∨ p1))) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249457310470468523465273014118 : ((p5 ∨ False) ∨ (p3 ∨ ((((False ∨ p4) → (p3 ∨ ((False ∨ False) ∧ p3))) ∧ (p2 → p1)) ∨ (p5 → ((((p2 → False) ∧ p1) ∧ p4) ∨ p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179197451379633006136492111471 : ((p3 ∧ (p4 ∧ (((p1 ∨ (p5 ∨ True)) ∧ (True ∧ (p1 ∨ p5))) ∧ False))) ∨ (((p2 → (p2 ∧ (True ∨ ((p2 ∨ p1) → True)))) ∨ p5) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310199895154892275899685126745 : (p2 ∨ ((((p1 ∨ ((p4 → p5) → ((p2 ∨ p3) → p4))) → False) ∧ p4) ∨ (True ∨ (True → ((((p5 ∨ (p3 ∨ p4)) → False) → p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152650233886617947550047008308 : (((False → False) ∧ (((((p1 → p1) ∨ (p3 → (p2 ∨ p4))) ∨ p4) ∨ ((p3 ∨ (p1 ∨ p4)) → p3)) ∧ p3)) → (((p3 ∨ p5) → p1) ∨ p3)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913177382248931848436913632849 : (((((p4 ∧ False) → (((p3 ∧ (p3 ∧ (((False ∧ p3) ∨ p2) ∨ (p3 → p4)))) ∨ p1) ∧ p2)) → ((p2 ∧ ((False → p2) ∨ p3)) ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ False) → (((p3 ∧ (p3 ∧ (((False ∧ p3) ∨ p2) ∨ (p3 → p4)))) ∨ p1) ∧ p2)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64598781245335483701860735255 : ((p1 ∨ ((True → p5) ∨ ((p1 → (False → True)) ∧ (p2 ∧ (True ∧ (p3 → (p4 ∨ (((p4 ∧ (p4 → (p4 ∨ p4))) → p1) ∧ p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700981377574452008953537680586 : (((((False ∨ (False ∨ (p2 ∧ (p4 ∨ (p3 ∨ False))))) ∨ p1) ∧ (((((False → (p2 ∨ p5)) ∧ False) ∧ (p2 ∨ p2)) → (False → p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620215678843855215353031255162 : (((((p4 ∧ p1) ∨ (((((p2 ∧ (p3 ∨ p4)) ∧ p3) ∨ True) ∨ ((p2 → ((p2 ∨ (p5 ∧ p2)) ∧ False)) ∧ (p2 → True))) ∨ p1)) ∨ p5) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147868796405527306672824966247 : (((p3 → (((p3 ∧ (((((p2 ∧ False) → (p4 → p1)) ∧ p1) ∨ True) ∨ p1)) ∨ (p3 ∨ p3)) ∧ p5)) → p5) ∨ (True ∨ (p4 ∨ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130474122516371153428679043120 : (((True → ((((p4 → p3) → (p1 ∨ (p3 ∨ (False → p2)))) → (p4 ∧ p1)) ∧ (True → p3))) ∨ (p2 → (p4 → p4))) ∧ (p3 ∨ (True ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158171395431091909879247403721 : ((((True ∨ (p1 ∨ p4)) → p4) → (True ∧ (((p2 → (p3 → (p1 → p5))) ∨ True) ∧ (p1 ∧ p3)))) ∨ (p3 → (p1 → ((p1 ∨ p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135461424471940089099181487631 : ((((p4 ∨ (False ∨ ((p5 ∨ p5) ∧ ((((p4 ∧ (False ∧ p1)) → p4) ∧ True) ∨ p4)))) → p2) → ((p1 → p1) ∧ p4)) ∨ ((p4 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135479043060987893655503462148 : (((((False ∨ ((p1 ∧ False) → p5)) ∨ True) ∨ ((((p3 ∧ p4) ∧ p5) ∨ (True ∧ p2)) → True)) → (p5 ∨ (p4 → p4))) ∨ (p3 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345510366334633661023533836668 : (p3 → ((((((p1 ∧ True) ∧ p2) ∧ p4) ∧ ((p5 ∨ (p5 ∧ (False ∧ False))) ∧ True)) ∨ (((False ∨ (p4 ∧ (p4 ∧ p1))) → p3) ∨ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110979705025800569125399979019 : ((((((p1 ∨ ((p2 ∧ p1) ∨ (p3 ∧ ((False ∧ (True ∧ p4)) → p5)))) ∨ p3) → ((p2 ∧ True) ∨ p5)) → (p4 ∧ True)) ∧ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704217671587032833251225425298 : ((((((p2 → (p1 → (False ∨ p4))) ∧ p5) → (p3 ∨ p3)) → (p2 → ((((p3 → False) → (p4 → (p3 ∨ False))) ∧ p2) → (False ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66361910421553035130331213871 : ((p5 ∨ (False ∨ ((p3 → (p1 ∧ p1)) ∨ (((((((p2 ∧ False) → (p5 ∧ (p1 ∧ True))) ∧ (p4 → p1)) → p1) ∧ True) → p2) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786502850610137246578387399214 : (((p4 ∨ ((((p4 ∨ p4) ∨ ((p5 ∧ (p4 → p2)) ∨ (False ∧ True))) ∨ False) → ((p1 ∨ True) → (p1 ∧ ((p5 ∧ p2) ∨ (p5 → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307450950366512863776064585750 : (p1 ∨ (p5 ∨ ((((p5 → False) → True) ∨ p5) ∧ ((((True ∧ ((p5 ∧ p2) ∧ False)) ∨ (((p3 ∨ False) ∨ (p5 → p1)) ∨ p2)) ∧ p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675548763884717993578885529694 : ((((((p5 ∧ False) ∧ ((((True → False) ∧ (False ∧ True)) ∧ ((False ∨ p3) ∨ False)) ∧ p1)) ∧ (False ∧ p3)) ∧ ((p3 ∧ p5) ∨ (p5 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192094035880540202774788228771 : ((p4 → ((((p5 ∧ p2) ∨ True) ∨ True) ∧ (p5 → p1))) ∨ (((p4 ∨ p2) ∨ ((p1 → (p3 → p3)) ∧ (True → p5))) → (p2 ∨ (p1 ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299114982025984629238960066505 : (False ∨ (((p2 ∨ (((True ∨ (False ∨ p2)) → (p1 ∨ p1)) ∧ (p1 ∨ (((((p3 → p1) → True) ∧ (p4 → p1)) ∨ False) → True)))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52957673071208089531487485331 : ((((p1 ∨ ((False ∨ ((p2 ∧ True) ∨ (p5 ∧ p3))) ∨ p2)) ∨ False) ∧ (p1 → ((p5 → True) ∧ (False → ((True → (p3 ∧ False)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54045825524682804648231646110 : (((((p4 ∧ p1) → (True → p3)) ∧ ((False ∧ True) → False)) → (p2 → ((True ∧ ((p3 ∧ p5) → p4)) ∨ (False ∧ ((True → False) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114436861077708339506249390582 : (((p3 ∨ (((((p3 ∨ p2) ∨ False) → (((p1 ∨ p2) ∧ p2) ∨ True)) ∧ True) ∨ (p1 ∨ p2))) ∨ ((False ∧ False) → (p2 → True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596577152591734682979815524803 : (((((False ∨ (((p3 → (p3 ∧ p2)) → p2) ∨ False)) → (p1 → (((p1 ∨ (p1 ∨ (((p5 → p3) ∧ p2) ∧ p1))) → p5) ∨ p5))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88300923358908112258899638966 : (((p3 → ((p2 → p2) ∧ p1)) ∧ ((((True → p3) ∧ (True ∨ (p5 ∨ (p1 → (False → True))))) ∧ p5) ∧ ((False ∧ p3) → (False → p4)))) → p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h19 := h8 h18
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h25 := h8 h24
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57677986776000444381454766896 : ((((p2 → p1) ∨ True) → (((((p4 ∨ p4) → ((p4 ∨ p5) ∧ p1)) → p5) → p4) ∧ (((p4 → (p1 ∧ p1)) → p2) ∨ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471530690187300654307349241086 : ((((((p3 ∨ (p5 ∨ p5)) ∨ ((p1 ∧ p5) → (p4 ∨ False))) ∨ p5) ∨ (((False ∨ p2) → ((p1 ∧ p4) ∨ (p4 → (True ∨ True)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94988093336105881732933222440 : ((p4 ∧ ((((True ∨ (p4 ∨ p5)) ∧ (p4 ∨ p2)) ∧ (((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) → False)) ∧ p5)) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h12
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h22 := h7 h18
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h25 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h26 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h30 := h7 h26
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h32 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- Implications on the right can always be decomposed.
          intro h34
          -- Implications on the right can always be decomposed.
          intro h35
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h36 := h7 h32
        -- False on the left can always be used.
        apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h38 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h39 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h40
          -- Implications on the right can always be decomposed.
          intro h41
          -- Implications on the right can always be decomposed.
          intro h42
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h43 := h7 h39
        -- False on the left can always be used.
        apply False.elim h43
      case inr h44 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h45 : ((p3 → (p1 ∧ (p3 → p1))) → (p1 → (p4 → (p5 ∨ p1)))) := by
          -- Implications on the right can always be decomposed.
          intro h46
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h49 := h7 h45
        -- False on the left can always be used.
        apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90216679242998979665757377036 : (((True ∨ (p3 → True)) → ((p3 → (((p2 ∧ ((p2 ∧ (p2 ∧ (((p5 → p1) ∧ p4) ∧ (True → True)))) ∨ p5)) ∧ p2) → False)) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p3 → True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315911910007108692192972034321 : (p3 ∨ (True ∧ ((p1 → (p5 ∧ p4)) → (((p1 → p3) ∨ (((p4 ∧ p2) ∨ (False ∨ True)) ∨ p5)) → (((p2 ∨ p4) ∨ p1) → (p1 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- False on the left can always be used.
              apply False.elim h13
            case inr h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- False on the left can always be used.
              apply False.elim h24
            case inr h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h37 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61170125465709928268783454762 : ((False ∧ ((p1 ∧ (p1 → p4)) ∨ ((((p2 → ((False ∨ True) → ((p5 ∧ p5) → p1))) ∧ (p5 ∧ ((p4 ∨ p5) → p5))) ∧ p4) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259021268064031696282506985805 : ((True → p4) → (((p5 ∧ (((p5 ∧ p4) ∨ p4) → ((((((p2 ∨ True) → p2) ∨ False) ∨ p2) → p4) ∧ p2))) ∨ True) ∧ (False → (True ∧ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135427613686912170335729726456 : (((False ∨ (((p4 → ((p5 ∧ ((False ∨ p1) ∨ p2)) → p1)) ∨ p3) ∧ ((p2 ∧ p2) → p3))) ∨ ((p2 → p5) ∨ p1)) ∨ ((p2 ∧ False) → p5)) := by
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
theorem thm_5_vars_244494948737373187991012810613 : ((False ∧ p3) ∨ ((False ∧ (p5 → (((((p1 ∧ p4) ∨ (False → p3)) ∧ (p5 ∧ False)) ∨ (True → (False → (False → (p4 ∧ p5))))) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613484366532536408070107921240 : (((((False → (p4 ∨ ((p2 ∨ (p1 ∨ (p3 ∧ p2))) ∨ ((p1 → (False ∨ ((p3 ∧ False) ∨ False))) ∧ (True ∨ False))))) → (p2 → p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655319621205660365646016609592 : (((((p5 ∨ (False ∧ (((p1 → p2) ∧ (p5 ∨ ((p3 ∨ (True ∨ ((True → p3) → p5))) ∧ True))) ∨ False))) ∧ (p2 ∧ True)) ∨ (p5 → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305293038155331384281857433021 : (p1 ∨ ((((p3 → (((((False → p4) → p5) → p4) ∧ p3) ∨ (p2 ∧ p5))) ∨ (p1 → p3)) → p4) ∨ (((p5 → (p1 ∧ p4)) ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300133420186936796988098615957 : (False ∨ (((True → False) → (((p1 → (p2 ∨ ((((p3 → (p1 ∧ p5)) → p2) → p4) ∧ ((p3 ∨ False) ∨ p3)))) ∧ p4) ∧ p2)) ∨ (p2 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
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
theorem thm_5_vars_252007683432334921777464706015 : ((p4 → False) ∨ (p3 ∨ ((((True ∧ (p5 → (True ∧ ((p3 ∧ (False ∧ (p4 → p4))) ∧ True)))) ∨ p5) → (((p3 ∧ False) ∧ p2) ∨ True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_388285798265732940509795490142 : (((((False ∧ ((False ∨ p5) ∧ ((p3 ∨ (p1 ∧ p3)) ∨ (p3 ∧ (((p4 ∨ True) ∨ True) ∨ False))))) ∨ ((False ∨ p4) ∨ (p4 → p4))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_207944093708849293870343119981 : (((False → (True → True)) ∧ (False ∨ p3)) → (True → ((p5 ∧ ((p2 → (p5 ∧ p1)) → ((p3 ∧ (False → p4)) ∧ p1))) → (p4 → (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the left can always be decomposed.
  let h11 := h3.left
  let h12 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185353399628335494447802126542 : ((p4 ∧ ((p3 ∨ True) ∧ (p3 ∨ ((p4 ∧ (p1 → p3)) ∨ p3)))) ∨ (((p3 ∧ (p4 → (p2 ∧ ((p5 ∨ p2) ∨ True)))) ∧ (p3 → p3)) → p3)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213263739524338866836045393380 : ((((p3 ∨ p1) → p3) ∧ p2) ∨ (p2 → (((True → p3) → (((((p2 → p2) ∨ p1) → (p5 ∨ True)) → (True ∧ p3)) ∨ (False ∧ p4))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186320969707058391417773209944 : (((((p1 ∨ (p2 ∨ p3)) → (p3 ∧ False)) → (p2 ∧ p5)) → False) → (((((True ∧ p2) ∧ (p4 ∧ p3)) → p4) ∧ p3) → ((True → p4) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 ∨ (p2 ∨ p3)) → (p3 ∧ False)) → (p2 ∧ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ (p2 ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (p2 ∨ p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h5
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675574501664168550498197139234 : ((((((((p2 ∧ (p4 ∨ p1)) ∨ (p2 → ((True ∨ False) → p2))) ∨ (True ∧ False)) ∧ p3) ∨ (p2 ∨ p5)) ∧ (p4 → ((False ∨ p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1967385569620297490474952912 : (((p4 ∧ p5) ∨ (((p3 ∨ p3) ∨ (((((p4 → p4) ∧ True) ∧ p3) → (p1 → p4)) → p1)) → p3)) ∨ ((True ∨ p4) → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682115317706335450543598465473 : ((((((((((p4 ∧ (p5 → (False ∨ p2))) → p3) → p4) → (True → p2)) → p2) → p5) → False) ∧ ((p4 → False) ∨ (True ∨ (True ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299341565724597514023785080915 : (False ∨ (((p5 ∨ (p4 → p3)) ∧ (((p3 ∨ p4) ∨ (((False → p4) ∧ (((False ∧ ((p4 → False) ∨ True)) ∧ p2) ∨ p3)) ∧ p5)) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351660758452026587529180006477 : (p4 → (((True → ((p5 ∧ ((((p2 → p3) → p5) ∨ p4) ∨ (p3 ∨ True))) → True)) ∨ p1) → ((p2 ∨ (True → False)) ∨ (p1 ∨ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475670843069847050478179115362 : ((((((p5 ∧ (((p2 ∧ p3) ∧ p2) ∧ p3)) ∨ p3) ∧ p4) ∨ (p4 → (((p5 → (p2 ∧ p4)) ∧ (p4 ∧ p3)) → (True ∨ (True ∧ p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327056981865689105084137925405 : (True → (((p1 ∨ ((p5 ∧ (p5 ∧ p3)) ∧ True)) ∨ ((p1 ∨ (((p5 ∨ (p5 ∧ p3)) ∨ (True ∨ p3)) → (p4 ∨ True))) ∨ (p1 ∨ p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135094009646643734108596424540 : ((((p2 ∨ (p2 ∧ (p1 → ((False ∨ True) → p5)))) ∧ (((p4 → p5) ∨ (p5 ∧ (p2 → True))) → False)) ∨ (p5 → p5)) ∨ ((True → p4) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61390264969927768780480169861 : ((p1 ∧ (((p4 ∧ ((((False ∨ p1) → p4) ∧ p2) ∨ False)) ∨ ((p3 → p5) ∨ ((p5 ∨ (((p3 ∧ p2) → p3) ∨ p2)) → p4))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244006143040370133888486950068 : ((True ∧ p2) ∨ (((((((p4 → p1) ∧ (((False → p2) → ((p1 → p1) ∧ True)) ∨ p5)) ∨ (p1 ∧ p1)) → p4) → (p1 ∨ p3)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751160732530642200211134723943 : (((True ∧ (((p4 → p4) ∧ False) ∨ (((p2 ∧ True) ∨ (False ∨ ((p2 ∨ p3) ∨ (((p1 ∧ p5) → (p2 ∨ (False → p3))) → True)))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106399908368481318434623386048 : ((((False ∨ p5) → (((p4 ∨ p2) ∨ True) ∧ (p2 ∧ p2))) → (p1 → (p1 ∧ (((True ∨ (p5 → p1)) → p2) ∨ (p1 ∧ True))))) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324483193190833286188445520584 : (p5 ∨ (((p5 ∧ (p2 ∨ p2)) ∨ p2) ∨ (((p3 ∨ (p2 → (p2 → (p1 → ((p1 ∧ (p2 ∧ True)) ∨ (p1 ∧ p3)))))) ∨ p1) → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_158412049543862457513051387725 : (((p1 ∧ p3) ∨ (p4 → (False ∨ ((p5 → p3) ∨ ((p4 → (True ∧ (False ∨ p3))) ∨ (p4 ∧ p4)))))) ∨ (((p2 ∨ p1) ∧ True) ∨ (p1 ∧ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259443468332541777285918596729 : ((False → p4) → ((((p4 → p2) ∧ ((True → (True ∨ ((p4 → p3) ∧ p1))) ∧ (False → (p2 ∨ ((False ∧ p1) ∧ p5))))) → p4) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42947396404399655644979294778 : (((p4 → (True ∧ ((True ∧ p3) ∨ (p5 ∧ (p2 ∨ (((((p2 → (p1 ∨ p1)) ∨ p4) ∨ (p2 ∧ (p2 ∧ p3))) ∧ False) ∨ p3)))))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66276722617499618262207162973 : ((p5 ∨ (((p2 ∨ p3) → p3) → ((p3 → ((p1 → (False ∨ (False ∨ ((p4 → False) ∨ False)))) → True)) → ((p3 → False) ∨ (True ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_497877597351910406641507166320 : ((((True ∨ (True ∧ p4)) ∧ (((p4 ∧ ((((p3 → (p3 ∨ True)) ∧ p2) ∨ p3) ∧ False)) ∧ (p1 ∨ ((p3 → p1) → (p1 → p4)))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45897041546176884696015262978 : (((p4 → (((p1 ∨ False) → (((((p1 ∧ p5) → ((((p5 ∨ (False ∧ p2)) → p4) ∨ p5) ∨ False)) ∨ p3) ∧ True) → True)) ∧ False)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1539278619632164668116066905 : (((p1 → p1) → ((p3 ∧ (((p1 ∨ (((p5 ∨ p2) ∧ (((p1 ∨ False) → False) → True)) → p2)) ∧ False) ∨ False)) ∨ p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206995184294301236615413972919 : ((((False → True) ∧ (True ∨ True)) ∧ p5) → ((p3 ∨ p5) ∧ (p4 → (((p4 → ((True ∧ (p1 → False)) ∨ True)) ∧ (p4 → False)) ∨ (p2 → p4))))) := by
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
  cases h5
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644304508768734663738577780 : (((((p4 ∧ ((p5 ∨ ((p2 ∧ (p2 ∨ p5)) → p3)) ∧ p2)) → (p5 ∧ (p5 → (True ∧ p5)))) ∧ p2) ∨ ((True ∨ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51156300882955129195946473771 : ((((p2 ∨ (((p2 → ((True ∨ (True ∨ True)) ∨ (p2 ∨ p1))) → (True ∨ p1)) ∧ p2)) → p5) ∨ (p1 ∧ (p4 ∧ ((p1 ∨ p4) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21409692857451819250550637389 : (((((((True ∧ (p1 → p2)) ∧ p3) ∧ True) → False) ∨ p4) ∨ (p1 ∨ ((p5 ∨ (p1 ∨ (p1 → p1))) ∨ (p5 ∨ (p2 → (p2 ∧ False)))))) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



