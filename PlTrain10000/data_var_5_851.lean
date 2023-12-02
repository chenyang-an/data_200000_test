variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178990894474844039228009265890 : (((p4 → p3) ∨ ((((False → p2) ∨ (p5 ∧ True)) ∨ True) → (p4 → p5))) ∨ ((((True ∧ (p4 ∧ (p1 ∨ p2))) ∧ p5) ∧ p3) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136856854246856795213988916081 : (((p5 ∧ True) ∨ ((p3 ∨ (p1 → ((p1 ∨ False) ∧ (((p4 ∧ (p4 ∨ ((p4 ∧ p5) ∧ p3))) ∨ p4) → p3)))) → p4)) ∨ (p5 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112329181775181451216857002202 : (((p4 → (((((p1 → (True ∧ (p4 → False))) → (((p4 ∧ (p2 → p2)) ∨ p4) ∨ (p3 ∨ True))) ∧ p2) ∨ p3) → p1)) ∨ True) ∨ (p5 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264428153346306458163509223561 : (True ∧ ((((p3 → True) ∨ p3) ∨ True) → ((((p3 ∧ ((((((False ∧ p2) ∧ p3) ∧ p1) → p1) ∨ p3) → p4)) ∨ True) ∨ p4) ∨ (p4 ∧ p2)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231655043814576990178973228967 : (((False ∧ p4) → p4) → (((((p1 ∨ ((True → (True → p5)) ∨ (p4 ∧ p5))) → False) ∧ (False → True)) ∧ ((p2 ∧ (p4 ∧ True)) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41928849032326129983193695110 : ((((p2 ∨ (p2 → p5)) → (((p3 → (((False → ((((False ∨ True) ∨ p5) ∨ True) → p5)) ∨ p1) → False)) ∧ p1) ∧ (p4 → p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696468631751502314913310200070 : ((((((p4 ∨ ((p2 ∧ p4) → False)) ∨ (False ∨ (p5 ∧ p2))) ∧ True) ∧ (p4 → (p5 ∨ (((p3 ∧ (p1 → (p2 ∧ True))) ∨ p1) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769823370418131486692832141328 : (((p5 ∧ (p4 ∨ ((True → (True ∧ False)) ∧ ((((p2 → (p2 ∧ p5)) ∨ p4) ∨ (False → (True → (p3 → False)))) ∨ (p3 ∧ (p4 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157609331834889296078812220153 : (((((False ∨ (p2 → (((p3 ∧ p2) ∨ (p2 ∨ p1)) → False))) → p4) ∨ p4) ∧ ((p3 ∨ p3) ∨ p4)) ∨ (p4 ∨ (((p2 ∧ p3) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72108104297874022758921254013 : (((True → (((True ∨ (False ∨ (p5 → ((p4 → p3) → ((((True → p2) → ((True ∧ False) ∨ p4)) ∨ p1) → False))))) ∨ True) ∧ p5)) ∧ p1) → p5) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615956749344297594809074795303 : ((((((((p2 → p2) ∧ (True ∨ p2)) ∨ (((p4 ∧ False) ∧ p4) → p4)) ∨ p2) → ((True ∧ ((p3 ∧ p2) → p3)) ∧ (p5 → p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117396561413069837712939406820 : ((p1 ∧ ((((p5 → ((p4 ∨ p5) ∧ p1)) → p4) → ((((p1 ∨ p5) ∨ p1) ∨ (((p1 ∨ p5) ∧ p4) → p4)) ∨ True)) ∨ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728971174893512294844118894400 : (((((p1 ∨ p3) ∧ True) → (p4 ∨ ((p5 ∨ (((True ∧ (((True ∨ p1) ∧ (True ∨ ((False ∧ False) → p2))) ∨ p3)) ∨ p1) ∧ False)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724152197114243048234316323111 : ((((p2 ∧ (False → p1)) ∧ (p5 ∧ ((((p1 ∧ ((False → p3) ∨ True)) ∨ p1) ∨ (True ∧ (p1 ∨ p5))) → (p4 ∧ ((p2 ∨ p1) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655026981477586021350171354985 : ((((((p2 → p1) → (True ∧ ((False ∨ (p3 → (False ∧ ((True ∨ False) ∧ ((p5 ∧ (True ∧ p2)) ∧ True))))) ∧ p5))) → p2) ∨ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56662474076574273695989780453 : ((((p5 ∨ p5) ∧ True) ∧ (p3 ∧ (((True ∨ ((p3 ∨ (p3 ∨ (p1 → (p3 ∧ p4)))) → p1)) ∨ (True ∨ p3)) → (p4 ∨ (p4 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52290946187411674225581402164 : (((((p3 ∧ ((p1 → ((True ∨ p1) → (True ∧ p1))) ∧ p5)) ∧ p3) ∧ True) ∧ (p5 ∨ (((p3 ∨ False) ∨ (False ∨ (p3 ∨ p2))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213115562841649093885101252132 : ((((p5 ∨ True) ∧ p1) ∧ False) ∨ (((True ∨ p1) → ((((p5 ∧ p1) ∨ p1) ∨ p3) ∧ p1)) → ((True ∨ p1) ∧ (((p5 ∨ p4) ∧ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301162607897703769741820438018 : (False ∨ ((p5 ∨ (p5 ∧ (p5 ∧ (False ∨ (True ∨ False))))) ∨ ((p3 → (True ∨ ((p5 ∨ True) → (((p5 ∧ p3) ∧ p1) → (p1 ∧ True))))) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323699331687993520559368740574 : (p5 ∨ ((((((p2 → False) ∨ (p2 → p1)) ∨ True) ∧ ((p4 → (False ∨ (p4 ∧ (False ∨ p3)))) ∧ p4)) ∨ False) → (True ∧ ((p1 ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h4.left
        let h8 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
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
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164549123241248659578048240414 : ((((p4 ∨ (((p1 → p4) → (p5 ∨ p4)) ∧ p4)) → ((True ∧ p5) ∧ (p2 ∨ p2))) ∧ p2) ∨ (((p5 ∧ p2) → True) ∨ ((True ∨ p1) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336223599621039000476947183549 : (p1 → ((((((((False ∧ False) ∨ (p4 ∨ ((p2 → (True ∨ p4)) → p1))) → True) → (p1 ∨ True)) → p4) ∨ p5) ∨ ((False ∨ True) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341096435924530671471811378678 : (p2 → ((p2 → (p1 → (((((p2 ∨ (p3 → p2)) → True) ∧ (p5 → False)) ∧ ((True ∨ p4) ∨ p1)) → (p4 → (True ∧ (False ∧ p4)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110755419278985805238987733598 : ((((p3 ∧ ((p1 ∧ (((p2 ∨ p4) → ((((p4 ∧ (p2 → False)) → p3) ∨ True) ∨ p4)) ∨ (p5 ∨ p2))) ∧ p5)) ∧ p1) ∧ p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615467124311365091792628175952 : (((((((p5 ∨ ((p5 ∨ (p3 ∨ (((p4 → p3) → True) ∧ p4))) → p2)) → True) ∨ False) → (p2 → ((p2 ∨ (p4 → p1)) ∨ p2))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41265611671867517806008480627 : ((((p3 ∧ ((p5 ∧ (True ∨ ((p5 ∨ True) → (p3 ∨ (False → (p4 ∧ (p1 ∧ p1))))))) ∨ p5)) ∨ (False ∧ ((True ∧ p5) ∧ False))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233741581273188627911092933595 : ((p3 ∨ (p4 ∧ p4)) → ((True ∧ (p2 ∧ (p1 ∨ p1))) ∨ (((p5 ∨ p4) → p4) ∨ (((p3 ∨ (p2 → False)) → (p2 → False)) ∨ (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98818061016609323953940335077 : ((True → (((True ∧ True) ∧ (p2 → (((p4 → (True ∧ ((p1 ∧ True) → (((p4 ∨ p5) ∨ p1) ∨ True)))) ∨ (True ∧ False)) ∧ p3))) ∧ p5)) → p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105153593238854595037197172951 : ((((p4 ∨ (p2 ∧ False)) ∨ (p2 ∨ (((p1 ∧ p4) → ((True ∨ (False ∨ p1)) → False)) ∨ (False ∨ p1)))) ∨ ((False → p3) ∨ p4)) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125460994633846035742556153021 : (((True ∨ p3) ∧ (False ∨ (((True → True) ∧ True) ∨ (((p2 ∨ ((p5 → p2) → ((p4 ∧ p1) ∧ True))) → (p5 ∨ p3)) ∨ p4)))) → (p2 ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134556324942347168326415813600 : ((((p2 ∧ (False ∧ (((p5 → (p1 → (p5 ∧ ((((p1 → p2) → p3) ∧ p2) → True)))) ∧ p1) ∨ False))) → p4) → p5) ∨ (p3 → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320455873389155082127581906702 : (p4 ∨ ((p5 ∨ p5) → (((True → ((p2 ∧ True) ∧ False)) → (((p1 → (p4 → p5)) ∧ ((p1 → False) ∧ True)) ∨ (p2 ∨ (p3 ∨ p2)))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
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
  case inr h7 =>
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
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760733193527301060019592961763 : (((p2 ∧ (False ∨ (((p5 → p5) ∨ (p4 ∨ (p5 ∨ (False → ((p2 → True) ∧ p1))))) ∧ (True ∧ (((p1 ∧ (p2 → p3)) → p5) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653681712843863831694603478344 : (((((((((p5 ∨ (((p1 ∨ p2) ∧ p1) ∨ p4)) ∧ p5) → ((p5 ∧ p5) ∧ (p4 ∧ p4))) → (p1 ∨ p1)) → p2) ∧ p1) ∨ (p2 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314791613481726785406860981402 : (p3 ∨ ((p3 → ((((p5 ∨ (p2 ∧ p2)) ∨ p2) ∨ (p3 ∧ (p1 ∧ True))) → False)) → (((((p3 → (True ∧ p2)) ∨ p4) ∧ p1) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_249522992672189456248123323674 : ((p5 ∨ p1) ∨ (p2 → ((p3 → (p1 ∨ p2)) → ((p2 ∧ (p3 → (p5 ∧ False))) ∨ (False → ((False ∨ p4) → ((p1 ∨ (p5 ∧ p4)) ∨ p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262456133605998900774748167208 : (True ∧ ((p1 ∨ ((((p3 → (p1 → (((False ∨ (p2 → (False ∧ p1))) ∨ p4) ∨ p5))) → (p5 → False)) ∧ (True → p5)) ∨ (True ∨ p2))) ∨ p1)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_963907029632388582367945127047 : ((((p4 → p3) ∧ ((((p1 ∨ p5) ∧ p4) → ((p1 ∧ p3) ∨ p5)) ∧ (True → (((False ∨ p3) ∧ ((p5 ∧ p4) ∧ p4)) ∧ (True ∧ p3))))) → p4) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110769678124821086035809066769 : ((((p2 → (p5 ∧ ((p4 → (p2 → p3)) → (p4 ∧ (p3 → ((False ∨ ((p2 ∧ True) ∧ p3)) ∨ (p4 → p3))))))) ∧ p1) ∧ False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71264330463221653113916052791 : ((((p3 ∧ (p4 ∨ p3)) ∨ (((p5 → p4) → False) ∧ ((((True ∧ False) → p1) → p3) ∧ (True ∧ (((p1 → p3) → p1) → False))))) ∧ p2) → p3) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h16 : ((True ∧ False) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h19
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h20 := h12 h16
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336419507324381282976404967256 : (p1 → ((False ∨ ((False → ((((False → ((((p5 ∨ p5) ∨ p5) → p3) → False)) ∧ (p3 ∧ (p3 ∧ True))) → False) → p5)) → (p4 → p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78959708061989285823131129988 : (((p1 ∧ (True ∧ (((p3 ∨ p1) ∨ p2) → ((True → (p5 ∨ (p1 ∨ ((p1 → ((p1 ∨ p2) ∧ p4)) ∨ p5)))) → p4)))) ∧ (p3 → p2)) → p4) := by
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
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 ∨ p1) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (True → (p5 ∨ (p1 ∨ ((p1 → ((p1 ∨ p2) ∧ p4)) ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116745784451829317166956826935 : (((p4 ∧ p5) ∨ ((p2 ∧ (((p4 → p4) ∨ p5) ∨ (p1 ∧ p5))) ∨ ((((True ∧ (True → p1)) → (p5 ∧ p2)) ∧ False) ∨ True))) ∨ (False → p3)) := by
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
theorem thm_5_vars_58194780738200643371104885685 : (((p3 ∧ p5) ∧ ((p3 ∧ (False → p2)) ∧ (p3 ∨ (((p1 ∧ (p4 ∧ (p2 ∧ (False ∨ ((False ∧ p2) ∧ p5))))) ∧ p2) ∧ (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606224648774128747692901852952 : ((((((((p4 → p3) ∧ True) ∨ (p1 ∧ (p1 ∨ (((((True ∧ p5) → False) ∨ (p4 ∧ (p5 → p3))) ∨ True) → False)))) ∧ p1) ∧ p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200793548903079235540104437243 : ((p4 ∧ (p5 → (p5 ∧ ((p5 → p5) ∧ False)))) → (((True ∨ p3) ∧ ((False ∧ ((p5 → (p3 ∨ p1)) ∨ (p5 ∨ (p1 ∨ p1)))) ∨ p5)) ∨ p4)) := by
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
theorem thm_5_vars_150583363590701299465123659898 : ((((p1 ∨ p5) ∧ (((p3 ∧ (True ∨ (p2 ∨ (p2 ∨ (False ∨ p5))))) ∧ ((p3 ∨ p3) ∨ p1)) ∧ p3)) ∧ p4) → ((p2 ∨ (True → True)) ∨ False)) := by
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
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h26 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
            case inr h31 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h28
          case inr h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- False on the left can always be used.
            apply False.elim h34
          case inr h35 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h36 =>
              -- Disjunctions on the left can always be decomposed.
              cases h36
              case inl h37 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h38
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h39 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h40
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h41 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h42
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h5.left
    let h45 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h44.left
    let h47 := h44.right
    -- Conjunctions on the left can always be decomposed.
    let h48 := h46.left
    let h49 := h46.right
    -- Disjunctions on the left can always be decomposed.
    cases h49
    case inl h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h53
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h54 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h55
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h56 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h57
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h58 =>
      -- Disjunctions on the left can always be decomposed.
      cases h58
      case inl h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h61 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h59
          case inr h62 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h59
        case inr h63 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h59
      case inr h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h64
        case inl h65 =>
          -- Disjunctions on the left can always be decomposed.
          cases h47
          case inl h66 =>
            -- Disjunctions on the left can always be decomposed.
            cases h66
            case inl h67 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h65
            case inr h68 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h65
          case inr h69 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h65
        case inr h70 =>
          -- Disjunctions on the left can always be decomposed.
          cases h70
          case inl h71 =>
            -- False on the left can always be used.
            apply False.elim h71
          case inr h72 =>
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h73 =>
              -- Disjunctions on the left can always be decomposed.
              cases h73
              case inl h74 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h75
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h76 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h77
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h78 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h79
              -- True on the right can always be proven directly.
              apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149353121502618863904683659171 : (((p4 ∨ p1) → (True ∧ (p2 ∨ ((p5 ∨ (p1 ∧ ((p1 ∧ (((p3 ∨ p5) ∧ p5) ∨ p4)) ∨ p1))) ∧ p1)))) ∨ ((True ∨ p2) → (True ∨ p1))) := by
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
theorem thm_5_vars_147381671293422228862553097782 : (((((p4 ∧ False) ∧ (p4 → ((p4 ∨ p1) ∧ (p2 ∧ p1)))) ∨ (((p2 ∨ (True → p4)) ∨ p3) ∧ p2)) ∨ False) ∨ (p3 ∨ ((True ∧ False) → p2))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313154451110592092858430835120 : (p3 ∨ (((((p1 ∨ (True ∧ (True → (p2 ∧ (True ∨ p1))))) ∧ p5) → p5) ∧ ((p2 → ((p4 ∧ ((p1 → p4) → False)) ∨ True)) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136026968769083615820954477698 : (((((True ∧ p1) ∧ (p1 ∧ True)) ∨ (p4 → (p4 ∨ False))) → ((p5 → p3) → ((((p2 ∧ p2) ∨ p4) ∧ p2) ∧ p2))) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_863253338270174048819049641563 : (((((p2 ∧ ((((p4 ∧ (((False ∨ True) ∧ False) ∧ p4)) → p1) ∧ p5) → False)) ∨ (False → ((((p4 → False) ∨ p3) → p2) ∨ p2))) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((((p4 ∧ (((False ∨ True) ∧ False) ∧ p4)) → p1) ∧ p5) → False)) ∨ (False → ((((p4 → False) ∨ p3) → p2) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49273151976713511637239512773 : (((p3 ∧ (((True ∨ ((((p2 → p5) ∨ p4) → False) → p5)) ∧ (p2 ∧ (((p3 ∨ p1) → p2) ∨ p2))) ∧ p5)) ∨ (True ∨ (p4 ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638104516286691540323283608289 : (((((p2 → ((p2 → ((p3 → False) ∨ p3)) → False)) ∨ ((True ∧ (False ∨ p1)) ∧ (((p1 → (True → (p4 ∨ p5))) ∧ p5) → p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38375905005832329190771567926 : ((((p5 ∨ (((True ∧ ((p3 ∨ p1) → (p1 ∧ p1))) ∧ (False ∨ (p2 ∧ p3))) ∧ False)) ∨ (((False → p1) → (p5 ∨ p1)) ∨ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711361750845358691648847866953 : ((((p1 ∨ (p5 ∧ ((p5 → p1) ∧ True))) ∧ ((False → (((p4 ∧ (False → (p5 → p4))) → (p1 ∨ p4)) → p3)) → (True → (p5 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150087223520611912645971881601 : ((True → (p5 ∨ ((p3 → (p4 ∨ (True ∨ (p1 ∨ ((False ∨ p4) ∨ ((False ∨ (False ∧ p1)) → p5)))))) ∧ p4))) ∨ (False → (p4 ∧ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51256320805244102636724108319 : ((((p1 ∧ p1) ∨ ((p4 ∨ ((p4 ∧ (p3 ∨ p4)) ∧ False)) ∨ ((p3 ∧ (p2 ∨ p4)) ∧ p3))) ∨ ((((p5 ∨ p5) ∧ p4) ∨ p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206832327655768119597650515177 : ((p5 → (p1 ∧ (p1 ∧ (p5 ∧ p3)))) ∨ (((((((p3 ∧ p2) ∧ p5) ∧ p3) → (p5 ∧ (p4 ∨ True))) ∧ p1) → p3) ∨ ((p4 → p4) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89183521446643418081067275022 : ((((False → p1) → p2) ∧ ((((p2 ∨ ((p5 ∨ p5) ∧ p5)) ∧ (p3 → (p5 ∧ True))) → (((p4 → (True ∨ True)) ∨ p3) ∨ p5)) ∧ True)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190619929453476961715804060618 : (((p1 ∧ ((p5 ∧ ((p4 → p3) ∨ p4)) → p3)) → False) ∨ (((True ∨ True) ∧ ((p5 → ((p5 ∧ (p5 → p3)) ∧ p3)) ∨ (p3 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338420600005193395237606355104 : (p1 → ((p3 ∧ ((False → p5) ∨ True)) → ((p5 ∨ ((True → p4) ∧ (True ∧ (p2 ∧ (True ∨ (p3 ∨ p1)))))) → (p1 ∧ ((False ∨ p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h2.left
      let h18 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h2.left
        let h24 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h2.left
        let h29 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h2.left
    let h34 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h36 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h42 := h41.left
    let h43 := h41.right
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h2.left
      let h46 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h46
      case inl h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h48 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h42
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h2.left
        let h52 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h53 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h54 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h42
      case inr h55 =>
        -- Conjunctions on the left can always be decomposed.
        let h56 := h2.left
        let h57 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h58 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h59 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150254973880942675004899924574 : ((p3 → ((True ∨ (True → (p3 → (((p3 ∨ True) ∧ p5) ∧ True)))) → (((p4 ∧ p1) → (False ∧ p3)) ∨ p2))) ∨ (p4 → (p1 → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111674982282425899215777960537 : ((((p4 → (((True ∧ p2) ∨ (p3 → (((True → (p5 ∧ (p2 ∨ (p2 → p4)))) ∧ False) ∧ p5))) ∧ (p1 → True))) ∨ False) ∨ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148541840405226340234539281249 : (((p1 → ((p1 → (p2 ∧ ((False ∨ (p5 → p2)) → False))) ∨ p4)) → ((p2 ∧ (p2 ∨ True)) ∨ (p4 → p4))) ∨ ((False ∧ (True ∨ False)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168228431890114670158156446763 : ((((False ∧ p5) ∧ p3) → (p1 → ((False → ((p4 ∨ (p2 → True)) ∨ (p2 ∧ p1))) → True))) → (p4 → ((((p4 ∨ p2) ∨ p3) → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ p2) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336106295548398637749671704809 : (p1 → (((((p3 ∨ (((p5 ∧ (p4 ∨ p1)) ∧ ((False ∧ p5) ∧ ((p3 ∨ True) ∧ True))) ∧ p1)) ∨ (p1 ∧ (p3 ∨ p2))) ∧ p5) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168276540406724631948613542191 : (((p1 ∧ p3) ∧ (p5 → (True ∧ (p1 → ((p1 → p3) ∨ (((p5 ∨ p1) ∧ False) ∧ p5)))))) → (p2 → ((p3 ∧ ((p2 → False) ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800018770239200661338611448705 : (((p2 → (((((p1 → p1) → ((p1 → ((((p5 ∨ p4) → False) ∨ (p5 ∧ p5)) → p2)) → p4)) ∧ True) → ((p3 → p5) ∧ p5)) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732143075449513866059549943581 : ((((True ∧ p3) ∧ (((((True ∨ p1) ∧ p4) ∧ (p1 ∧ True)) ∧ p5) → (p3 ∨ ((((p2 ∧ (p3 ∨ p3)) ∨ p1) → (True ∧ False)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114058738728567854245749567970 : ((((((p1 ∧ (False ∨ (p5 ∧ (p4 ∨ (p1 ∨ False))))) ∨ p5) ∨ True) → (((p2 ∨ False) ∨ p5) ∨ True)) ∨ (True ∨ (p4 ∨ p5))) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164459936227730269476604775468 : ((((p3 ∨ (p5 ∨ (((p4 ∨ ((p3 → p3) → (p5 → False))) ∨ p5) ∨ p3))) ∧ True) ∧ p1) ∨ (((p4 → p1) → ((True → p4) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690770031670507761866860035468 : ((((((False ∧ ((p5 ∨ True) ∧ (p4 ∨ (p2 → (True ∨ p5))))) → (p2 ∨ p1)) → False) → (p4 ∧ ((p2 ∧ (p4 ∨ True)) ∨ (p4 ∧ p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p5 ∨ True) ∧ (p4 ∨ (p2 → (True ∨ p5))))) → (p2 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((False ∧ ((p5 ∨ True) ∧ (p4 ∨ (p2 → (True ∨ p5))))) → (p2 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h7
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769362582738622761061437447484 : (((p5 ∧ (True ∧ (p5 ∨ ((True ∨ (p3 → False)) → (((p3 ∧ (p1 ∧ ((True → False) → (p2 → (p5 → p4))))) ∧ p2) ∨ (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149181064705774607875120145239 : (((False → p4) ∧ ((((((p1 → p5) → False) ∨ p4) → p1) ∧ ((p4 → False) → (p1 → (p2 ∧ True)))) ∧ p3)) ∨ (p4 → (p2 ∨ (False → p5)))) := by
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
theorem thm_5_vars_133687638187730197401231984843 : ((((((p4 ∨ False) → (((p3 → (p5 → p5)) ∨ p1) → (p1 ∧ p3))) ∧ (True → p2)) ∨ ((False → True) ∨ p4)) ∧ True) ∨ ((p3 ∨ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_151408064495479758974944057076 : (((((p4 ∨ p3) → p3) ∧ ((p1 ∨ (((p5 → p5) ∨ p3) → p3)) ∧ (p5 ∨ (p1 → p5)))) ∧ (p2 → p2)) → ((p4 ∨ p2) ∨ (p3 → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155540359421322507877336963856 : ((((False → p4) ∧ True) → (((p2 ∨ p2) ∨ p2) → (((p5 ∨ (p4 ∨ True)) ∨ (False → p1)) ∨ p2))) ∧ (True ∨ (((p3 → p1) ∧ p2) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      let h5 := h1.left
      let h6 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800229610099027273596957344497 : (((p2 → ((((False ∧ p5) ∨ (True ∧ (p1 → ((p3 ∧ False) ∨ (p5 ∨ (((p4 → (False ∧ True)) ∨ p3) ∨ (True ∨ p5))))))) ∨ p4) ∨ p4)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305207845587738999616222462783 : (p1 ∨ ((((p3 ∧ p3) ∨ ((True → p2) ∨ ((p2 → ((((p3 ∨ p5) ∧ p1) ∧ True) ∧ p3)) → p2))) ∨ p4) → ((False ∧ p2) ∨ (p1 ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218649803671569227268361033205 : ((True ∧ ((p2 ∨ False) → p4)) → ((p4 ∨ ((p3 → (p5 ∧ ((True ∧ ((p1 → p2) ∧ p4)) ∨ p3))) ∨ p5)) ∨ (True → (p4 → (True → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44675525543908083725109119246 : (((((p1 ∨ (p4 ∨ False)) ∧ (True ∨ False)) → ((True ∧ p3) → ((p5 ∨ p5) ∨ (p3 ∧ (True ∧ (((p2 → p3) → p3) → p1)))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48408330302742349551814813653 : (((p1 → (p2 → ((p4 → (False ∧ (((((p1 ∧ (p4 ∨ True)) → p4) → (False ∨ (p3 ∧ p3))) ∨ p2) ∨ False))) ∨ p2))) → (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141244849299909021527612005182 : ((((True → True) → (p4 → (p2 ∨ p4))) → ((p3 ∧ (p1 ∨ (p4 ∨ (p5 ∨ ((p1 ∨ p3) ∧ (p4 ∨ p2)))))) ∧ False)) → ((p5 ∨ p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → True) → (p4 → (p2 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((True → True) → (p4 → (p2 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115857439585060364171331953719 : (((True → ((p3 → p3) ∧ p4)) ∧ (p1 ∨ (True ∧ ((((p1 ∨ False) ∧ p4) → (p3 ∧ (True ∨ p4))) ∧ ((p1 → p5) → p1))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1847219983196236874624744670 : (((p5 ∨ ((((p3 → (False → (p1 ∧ p3))) ∧ False) ∧ (p2 ∧ (p5 ∨ p1))) → (p1 → p2))) → (p2 ∧ p4)) → (False ∨ (False ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((((p3 → (False → (p1 ∧ p3))) ∧ False) ∧ (p2 ∧ (p5 ∨ p1))) → (p1 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592251105072243487970767540012 : ((((((p3 → (((((p5 ∨ (((p4 ∨ p1) ∨ p1) → p4)) ∧ p5) ∧ (True ∨ p4)) ∧ p1) ∨ (p2 ∧ p2))) ∨ p2) → (p3 ∧ p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71790509794298707256817311509 : (((p4 ∧ (p2 → ((((True ∧ p1) ∧ p3) ∨ (((False → p1) ∨ ((False ∨ p2) ∧ p3)) → ((p5 ∨ p2) → (True ∨ False)))) ∧ p1))) ∧ p2) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42707712152715687936063647410 : (((p5 ∨ ((p2 → (p1 ∨ p5)) → ((p3 ∧ (p3 → (p5 → (p2 → p2)))) ∨ ((((p5 ∧ p5) → True) → (p5 ∨ p5)) ∨ p4)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354615196051900259448393603069 : (p5 → (((((p2 ∨ True) → (p1 → (False ∨ ((p4 → p4) ∨ ((p4 → p2) ∧ p4))))) → (((p3 → p5) ∨ p1) ∧ (True → p2))) ∨ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650960761605289352610548163687 : ((((((p5 ∧ p3) → ((p5 ∧ True) → False)) ∨ (((p1 ∧ p4) ∨ p4) ∨ (((p2 ∧ p4) ∨ p5) → ((p5 → False) → p2)))) ∧ (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264784231768546927397403888865 : (True ∧ ((True ∧ False) ∨ (((((((p1 ∧ (False ∧ p3)) ∧ p2) → (p2 → False)) ∧ (p3 ∨ p4)) ∧ (False → (p5 → p1))) ∧ p5) ∨ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616508110696856075455908194639 : (((((p2 ∨ ((False → False) → (p4 ∨ ((p1 ∨ (p3 → True)) ∧ True)))) → ((((False ∨ (p5 ∧ p2)) → p1) ∨ True) ∨ (p3 ∧ True))) ∨ p4) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175064552537964161424329741706 : ((p2 ∧ (False → (p2 ∨ (((((p2 ∧ (p3 → p1)) → p3) → p4) → False) ∧ p3)))) → ((((p3 ∧ (p5 ∧ p4)) ∧ (True ∨ p2)) ∧ p1) → p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174629040925133288720469135084 : ((((p5 → p4) → (p3 ∧ p2)) → (True ∨ ((p1 ∧ p3) ∨ ((True ∨ p3) ∧ p5)))) → (p4 ∨ (p4 ∨ (p4 → (((p3 → p1) ∨ True) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60144810715161856610602460361 : (((p4 ∨ p2) → ((((p2 ∧ (((p4 → True) ∧ (p1 ∧ True)) ∧ p5)) ∨ ((p5 ∧ p1) → (True → p2))) → p4) → ((p5 ∨ p1) ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ (((p4 → True) ∧ (p1 ∧ True)) ∧ p5)) ∨ ((p5 ∧ p1) → (True → p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193065702752841122634815076075 : (((((p1 ∨ True) ∨ p3) ∨ p4) ∧ (p2 ∨ (p5 ∧ p2))) → (((p3 → p4) ∧ (p2 → (p2 → ((p1 ∧ ((p3 ∨ False) ∨ False)) ∧ False)))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h10 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h11 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h12 := h4 h11
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h13 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h14 := h12 h13
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h20 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h21 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h21
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h23 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h24 := h22 h23
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h30 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h31 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h31
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h33 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h34 := h32 h33
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h37
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h40 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h41 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h42 := h4 h41
      -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
      have h43 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h42, we can now drive its conclusion.
      let h44 := h42 h43
      -- We need to get the right conjuct of h44 based on <expert-advice>.
      let h45 := h44.right
      -- False on the left can always be used.
      apply False.elim h45
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- One of the premise coincides with the conclusion.
      exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164990121149602157284567159856 : ((((((p1 ∨ (p2 ∨ ((p3 ∧ p2) ∨ False))) ∧ False) ∧ False) → ((p3 ∨ p3) ∨ True)) → False) ∨ ((p4 → p4) ∨ (False → (p2 → (p2 ∨ p2))))) := by
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
theorem thm_5_vars_923774356661691352702716556683 : (((((p4 ∨ (p5 ∧ p4)) → (((p1 ∧ p3) → p3) ∧ (p3 ∧ False))) ∧ (((p4 ∧ (p3 → ((p4 ∨ p3) ∨ (p4 ∨ p1)))) ∨ p2) ∧ p4)) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p4 ∨ (p5 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ (p5 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156596784673276178428461352268 : (((((((((p5 ∨ True) ∨ p1) ∨ True) ∧ ((p2 ∧ p2) ∧ (True → True))) ∨ p5) → p5) ∧ p5) ∧ p1) ∨ ((True ∨ p1) ∨ ((p3 ∨ p2) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



