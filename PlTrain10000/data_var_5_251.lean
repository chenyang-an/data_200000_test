variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107051603452594435687876973571 : (((((p4 ∨ p3) ∨ p5) ∨ False) → (True → ((False ∧ (p5 ∧ ((((False ∧ (p2 ∨ False)) → p4) ∨ p3) → p1))) ∨ (True ∨ p5)))) ∧ (False → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65990937916307224457940665628 : ((p4 ∨ (p3 → (((True ∨ p3) → (p4 ∧ ((((p4 → p5) ∧ p2) ∨ p4) → ((p5 → (True ∨ (p4 ∨ (True ∧ False)))) ∧ False)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60599987439591193452991731319 : ((True ∧ (((p1 ∨ ((p3 → (((p3 ∧ (p4 ∨ p4)) → (p2 ∧ p3)) ∧ p1)) ∧ (p4 → ((False ∧ False) ∨ p5)))) ∨ True) ∧ (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232269044155504781012733087832 : (((p2 → p1) → p5) → (((False ∨ (False → p4)) → (True ∧ (True → (False ∧ (False → p4))))) ∨ ((True ∨ ((False → p2) ∨ (True → True))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3286770711680439269568734272 : ((p5 → False) ∨ ((((True → p1) → False) → ((False ∨ (p4 ∧ p1)) → True)) → ((((p4 → p3) ∨ True) ∨ p4) ∨ ((p1 → True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180247179139056428207977341866 : (((True ∨ (p2 ∨ ((p5 ∨ (p1 → (p1 ∨ (p5 ∨ p3)))) ∨ False))) → p2) → ((p4 ∨ p5) ∨ (p2 ∧ (p4 → ((False ∧ (p5 ∧ p3)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∨ ((p5 ∨ (p1 → (p1 ∨ (p5 ∨ p3)))) ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83388049155589479680762779741 : (((p3 ∧ (p5 → ((p3 ∧ p1) → (p2 ∨ ((p2 ∧ ((True ∨ p3) ∧ (p5 ∨ p3))) ∨ p4))))) ∧ (True → (p4 ∧ (p3 → (p5 ∧ False))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165492204550344826330435116778 : ((((p4 ∨ p1) ∧ ((p1 ∨ True) → (p1 ∧ (True ∧ True)))) ∨ ((p2 ∨ True) ∧ (p1 ∨ p5))) ∨ ((p4 ∨ p4) ∨ ((p4 ∧ False) → (p3 ∨ p3)))) := by
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
theorem thm_5_vars_685204097466159096038955453992 : ((((p5 ∨ (p5 ∧ ((((((False ∧ p2) ∨ (p3 ∧ p2)) ∧ p1) → p1) → True) ∧ (p1 → p3)))) ∨ (False ∧ (((False ∨ p3) ∨ True) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141454474082028088684974029398 : ((((p1 ∨ p4) → p2) ∧ (True ∨ ((((p2 ∧ (((False ∧ p4) → (p1 ∨ False)) → p2)) ∨ p5) ∨ p5) ∨ (p4 → p5)))) → ((True ∧ p2) → p2)) := by
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
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247316580813152321818694324688 : ((False ∨ False) ∨ ((p3 ∧ (True ∧ p2)) ∨ (p1 ∨ (True ∨ (True ∨ ((p5 ∨ (p5 → p3)) ∧ (((p1 ∧ p2) ∨ (p4 ∧ (p2 ∧ False))) ∧ p3))))))) := by
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
theorem thm_5_vars_63960738028927692643041296806 : ((False ∨ (((((p1 ∧ ((False ∧ (((((p5 ∨ False) → p4) ∧ p3) → p4) → p2)) ∧ (p4 → False))) → p2) ∨ (p4 ∨ True)) ∧ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66818269620664450038593401559 : ((True → (True → ((p2 → (((p3 ∨ p2) → p5) → (p1 ∨ (((True ∧ ((p5 ∧ p1) ∧ p1)) ∨ p3) ∨ (True → (False ∧ True)))))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_149781387137098626652166870771 : ((False ∨ (((((p2 → ((p1 ∧ False) ∧ (p2 → True))) → (p4 ∨ (p5 → True))) ∧ p4) → p5) → (p3 → p5))) ∨ ((p3 → (True ∨ p5)) ∨ p2)) := by
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
theorem thm_5_vars_621352497529779637937975787526 : ((((True ∧ ((p4 ∧ p5) → (True → (((((p1 → p3) ∨ p3) → ((p5 ∧ False) ∧ True)) ∨ (p5 ∧ (p4 ∧ p4))) ∧ (p4 → p5))))) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660996742776109521340882707517 : ((((((p2 → (True → (((p5 ∧ p2) → (((p4 → (p5 → False)) → (p1 ∧ False)) ∧ p5)) ∧ p4))) ∨ p2) ∧ (False → False)) → (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133656715003037770467857332250 : (((((p5 ∨ ((p1 ∧ (p1 ∧ ((((False ∨ p3) → (p1 ∨ True)) ∧ p4) ∧ p2))) ∧ p5)) → p3) ∨ (False ∧ p4)) ∧ p5) ∨ (True ∨ (p4 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166663335504016398336093026821 : ((p1 → (p1 → ((((p4 ∧ p3) ∨ (p5 → (p2 → (p5 ∨ p2)))) → p4) ∨ (True ∧ p1)))) ∨ (((p2 ∧ p1) ∧ (p5 → (p3 ∨ True))) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114606158977998486156947290457 : (((p1 ∨ (((p3 → (False ∧ (p5 ∧ ((p3 → p3) → False)))) ∧ p5) → (p3 → p2))) ∧ (p2 → (p1 ∨ ((True → False) ∧ True)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638493414266423416360184180117 : (((((((p5 ∨ (p4 → False)) ∨ False) → p4) ∨ ((p2 ∨ ((((True ∨ (False ∧ p2)) ∧ p1) ∨ p5) → p5)) ∧ (p5 → (p5 ∨ p1)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2217035211939296257070190293 : (((True ∨ (False → ((p2 ∨ (p5 ∧ p1)) → ((False ∨ True) → p4)))) ∧ (p4 → p1)) → ((((False → True) ∨ p3) → (p2 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215232708674091053268507448176 : ((False ∧ ((p1 ∨ p1) ∨ False)) ∨ (p3 ∨ (True ∨ ((True ∧ (((p4 ∧ ((p2 ∨ (p4 ∨ p1)) ∧ (p1 ∨ (p5 ∧ p3)))) → False) ∨ p5)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710807183408883013637848009626 : (((((p1 ∧ p1) ∧ ((p1 ∨ p5) → p4)) ∧ (p5 ∧ ((((p5 ∨ False) ∨ p4) ∧ ((p5 ∨ ((p4 ∧ p1) → (False → True))) ∧ p1)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646969794741635601563735683723 : ((((p3 → ((p5 ∧ (((False → p3) ∧ (True ∧ ((p4 → p1) ∧ ((True ∧ (True ∧ (p1 → p2))) → (p5 ∨ p5))))) → p4)) ∧ p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_898902615819893910945430095 : ((p3 → ((False → p5) → (((p5 ∧ ((p4 ∧ (p3 ∧ p3)) ∨ (p5 ∨ (p2 ∧ (False → (p3 ∧ p5)))))) ∧ (False ∨ True)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54254930758596882059582236365 : ((((p4 ∧ ((False → p3) → p1)) ∨ (p5 → False)) ∧ (p1 ∨ ((p2 → p5) ∧ (True → (((p4 ∧ p4) ∨ (p1 → False)) → (p2 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166772526262530171165456525755 : ((p5 → (((((True ∧ p3) ∧ True) ∨ ((True → (p3 ∧ p2)) ∧ p2)) ∨ p2) ∧ (True ∧ False))) ∨ ((p3 ∨ (False ∧ ((p2 ∧ p4) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151133442776940785778372095921 : (((((p2 → (p5 ∨ (False → ((p1 → p5) → p2)))) → (False ∨ (p4 ∨ (p5 ∧ p4)))) ∨ (p2 ∧ p5)) → p1) → (True ∧ ((p4 → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59180468520276953164721777994 : (((False ∨ p5) ∨ (p5 ∨ ((False ∨ (p3 ∧ (False → ((p3 → ((p1 ∧ p5) ∧ (p3 → (p2 ∧ p5)))) → ((True ∧ False) ∨ p3))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305162378402306304275173454107 : (p1 ∨ (((p1 → (p4 ∧ (((p4 ∨ False) ∨ (((p1 → ((False ∧ p2) → p3)) → p2) → False)) ∨ False))) ∨ p3) ∨ ((False ∧ (p5 → p5)) → p3))) := by
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
theorem thm_5_vars_249017028517054405432932594557 : ((p4 ∨ False) ∨ ((p3 ∧ (p1 → p5)) ∨ ((True → (p3 ∧ (True → p1))) ∨ ((((p3 ∨ p2) → p4) ∨ (False → ((p2 → p4) ∨ True))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728459589672554811489668806724 : ((((p2 → (p3 ∨ p5)) ∨ ((((p1 → (((((True → p1) → p2) ∨ (p1 ∧ (p2 ∧ p1))) ∨ p3) ∧ p4)) ∧ (False ∧ p4)) ∨ p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179209504981510936750673617999 : ((p4 ∧ ((p2 ∧ (p5 ∧ ((((p1 ∧ p3) ∨ p2) ∨ False) ∨ False))) ∨ False)) ∨ (p4 ∨ (True ∨ ((True ∧ (((True ∨ p4) → p5) → p2)) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149615118268284647418915134856 : ((p3 ∧ (p4 ∧ ((p2 ∨ (p4 → ((((False → (False ∨ p1)) → True) ∧ p3) ∨ p2))) ∧ ((p3 → p1) → p5)))) ∨ (p4 → (p4 → (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137807023425257879312175368269 : ((p2 ∨ (p4 → ((True ∧ (p2 → p4)) ∧ ((p2 → (((((p4 → (p1 ∨ True)) ∨ p1) ∨ True) → p4) → p1)) ∨ True)))) ∨ ((p5 ∨ True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775246755491125513530883193448 : (((False ∨ ((p4 ∨ p1) → ((False ∧ (((((True → p2) → p5) → (True ∧ True)) ∧ p3) ∧ (True → (True ∧ (p5 ∧ p4))))) ∨ (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164429316154509777638270892585 : ((p5 → ((p3 ∧ p3) ∨ (((True ∧ ((p3 ∧ False) → p2)) ∨ True) → (p1 ∨ (p2 ∨ True))))) ∧ (True ∨ (p5 → ((p5 → p2) ∧ (False ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41711448623779684593359762483 : ((((p4 ∨ ((p3 ∨ p4) ∧ (p2 ∧ p1))) → ((p2 ∧ ((p5 ∨ True) → (((p5 → p1) ∨ p3) ∨ ((p5 → p5) ∧ False)))) ∨ p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135971300488569370780438778864 : (((((((True → (p5 ∧ p4)) ∨ p5) ∧ p2) → p4) ∧ p1) ∨ (((((False → p3) → p1) ∨ p2) → p1) ∨ (p3 ∧ False))) ∨ (True ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52768513196408745922156572728 : ((((False ∨ ((((True ∧ (p3 ∧ p1)) ∨ p3) ∧ True) ∨ (True ∨ p5))) → p3) → (p5 ∨ (((((False ∨ False) ∧ True) ∨ p2) → p3) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615053419693165931814648204578 : (((((False ∨ ((False ∨ ((((p1 ∧ (p5 ∨ p1)) ∧ p3) ∨ (p1 → True)) ∧ False)) → (p5 ∧ p2))) → (p1 ∧ (p4 ∨ (True → p4)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_201148507532077437937422155879 : ((False → ((p5 ∨ (p4 → p5)) → (True ∧ p2))) → (p1 → ((p1 ∧ (((p3 → (p4 → (((p4 ∨ False) ∧ p2) ∧ p2))) ∨ False) ∨ True)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135280946164787219160085214642 : (((False → (((((((False → (True ∨ (p1 ∨ False))) → True) → False) ∧ False) ∧ p2) ∨ p3) ∧ (p1 ∧ True))) → (p5 → False)) ∨ (True ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197436499295898843055538815741 : ((((False ∧ (p1 ∨ p5)) ∧ p5) ∧ (p4 ∨ p5)) ∨ ((p3 ∧ (False ∨ ((True ∧ p1) ∧ (True ∧ p1)))) → (((p2 → p5) ∧ (p3 ∧ False)) ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263070820283060339789308379723 : (True ∧ ((((True ∨ (((p5 → (p5 ∧ p4)) ∨ p1) ∧ p4)) → ((((False ∧ (p5 ∨ False)) ∨ p5) ∧ p3) ∨ (p4 ∧ False))) ∧ p5) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_254066387611408358372288403612 : ((p2 ∧ True) → (p2 ∧ ((p4 ∧ (((p2 ∨ False) → (p4 ∧ False)) ∧ True)) → (((False ∨ p5) ∨ False) ∧ (False → (p3 ∧ (True ∧ (True → p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h11 : (p2 ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173948785574099408319648655813 : ((((p4 ∨ ((p5 → (p4 ∨ p2)) ∨ (p3 ∨ p2))) → (p5 ∨ (p5 → True))) → False) → (((True → p1) ∧ p2) → ((p2 ∨ (p5 → p4)) → p1))) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219898100341610544499077241537 : ((p4 → ((False → p4) ∨ p1)) → ((((((p3 ∧ ((p2 ∧ (True ∧ True)) ∨ False)) ∧ (p4 ∨ ((p3 → p1) ∨ False))) ∨ True) ∨ p1) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161057169435181586928142514437 : (((p4 ∧ (False ∨ p2)) → ((False → ((((((p2 ∧ p2) ∨ True) ∨ p4) → False) ∨ False) ∧ p1)) ∨ p2)) → ((True → (p4 ∧ (p1 ∧ p4))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800281553784052177035123348626 : (((p2 → ((((p1 ∨ ((((p2 → True) ∨ p5) ∨ p2) ∧ ((p5 → p5) → p2))) ∧ (p2 ∨ ((p5 ∨ p2) ∨ p3))) → (p5 ∨ True)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192843197504147899353413955319 : (((((True → p3) ∨ (False ∧ p5)) ∨ p3) ∧ (p5 ∨ p3)) → (p2 ∨ (True → (((p4 ∧ ((True → p2) → p4)) ∧ (p1 → p3)) ∨ (p1 ∨ True))))) := by
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
      cases h3
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215590762224608333265234619752 : ((p5 ∧ (p5 ∧ (p2 ∨ p5))) ∨ ((((p1 → (p4 → (p5 ∨ p2))) → p4) → (p2 ∨ (((False ∧ p2) ∧ p4) → p1))) ∨ (p4 ∧ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172038419740439955669387978608 : (((p2 ∨ ((p3 → ((p5 ∧ p3) ∧ ((p4 ∨ p3) → p2))) ∨ p4)) ∨ (False ∨ True)) ∨ ((False ∨ (p2 ∨ ((True ∨ False) ∧ p5))) → (p1 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96752079782340886465372052552 : ((p1 ∨ ((((p3 ∨ p2) ∧ (((((False ∧ (p1 ∧ p1)) ∨ (p1 → p2)) → ((p5 ∨ p5) ∨ (p2 ∧ p5))) ∧ p2) ∨ p3)) ∨ True) → False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p3 ∨ p2) ∧ (((((False ∧ (p1 ∧ p1)) ∨ (p1 → p2)) → ((p5 ∨ p5) ∨ (p2 ∧ p5))) ∧ p2) ∨ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329621133029711663618153462604 : (True → ((p5 → p2) ∨ (((((p1 ∨ p4) ∧ p2) ∧ (p1 ∨ p3)) ∧ p4) ∨ (((False ∨ p5) → ((p1 → (False → p4)) ∨ p5)) ∨ (p4 ∧ p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612366253666357275527119960471 : (((((p2 ∨ ((p1 → p2) ∧ (((p5 → (True → p3)) ∨ ((p4 → p1) ∨ (p3 ∧ ((p5 ∧ True) ∧ False)))) → p4))) ∧ (p3 → p2)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38630876286335448872256223458 : ((((((p3 ∨ p5) → False) → ((p2 ∧ False) ∨ p3)) ∨ (((((p1 → p2) ∨ p3) → p3) ∨ False) ∨ (p2 ∧ (False → (p2 ∨ p4))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114300274080609525863825352405 : ((((p4 ∧ (True → (((p4 ∨ p1) → (False ∧ False)) ∧ (True ∨ True)))) ∨ (p3 → (p1 ∧ p5))) ∧ ((p3 ∨ p4) ∨ (p1 ∨ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585764065111353398839211687415 : (((((((p4 → p2) ∧ ((((p2 → True) → p2) ∧ ((p4 ∧ False) ∧ (p5 ∨ ((p2 → p4) ∧ p4)))) → (p4 → p5))) → p1) ∧ p5) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337539884644290517147767886923 : (p1 → ((((p3 → True) ∧ (p2 ∨ (False ∧ False))) ∨ ((p5 ∧ (((p5 ∧ p4) ∨ p4) ∨ p2)) ∧ (True ∨ p2))) ∨ ((p3 → (p3 → p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356780880166337911049828637186 : (p5 → ((p2 ∨ ((p4 → True) → (p4 ∨ p4))) → (False ∨ ((((p5 → ((p5 → ((p2 → p4) ∨ p1)) ∧ False)) → p3) ∨ p5) ∨ (True → p2))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711872324769885983644384299079 : (((((p5 ∧ (p5 ∨ (p3 ∨ p1))) ∧ p1) ∨ (((p5 ∨ True) ∨ (((p5 → p3) ∧ (p4 ∧ (False → ((p1 ∧ True) → p3)))) ∨ True)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172007329620845741465944974391 : ((((((((p1 ∧ p5) ∧ True) ∧ True) → True) → p3) ∨ (p2 ∨ p2)) ∨ (False → p3)) ∨ ((p2 ∧ ((False ∨ False) ∧ (p4 ∧ p1))) ∧ (p5 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310770806651979925255841135202 : (p2 ∨ (((True → False) ∧ p5) ∨ ((p2 ∧ p5) ∨ (((p2 ∧ p3) ∨ p1) → (p3 ∨ ((p1 ∨ (True ∧ ((p2 ∧ p4) ∧ (p3 ∧ True)))) ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219906501199514030621292610380 : ((p4 → ((p2 ∨ p4) → p1)) → ((((True ∨ (p3 → ((p1 → p2) ∨ p1))) ∨ p2) ∧ ((True → p2) ∧ p5)) → ((False ∨ (p3 → p4)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134196601706303538020658859228 : ((((((p2 ∧ (p2 ∨ (p3 ∧ (True ∧ p3)))) ∨ p4) ∨ p5) ∨ (p1 → (p1 ∧ ((False ∨ p2) → (p4 → p1))))) ∨ p2) ∨ ((p5 ∧ p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245026462842320633871303429382 : ((p1 ∧ p4) ∨ (True → ((p5 ∧ ((((False ∧ False) ∨ ((False ∧ p1) ∨ p4)) ∧ p2) ∨ True)) → (True → ((((p5 ∧ p3) ∨ False) ∨ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192906286524013348460241498661 : (((((p5 ∨ (True → p5)) ∧ p2) ∧ True) ∨ (p5 → p4)) → (p5 → ((p2 → (p2 ∨ ((False ∨ p2) → p2))) → ((p4 ∨ True) → (p1 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114015488305272293205424321744 : (((((p2 ∨ ((p2 ∨ ((((False ∧ True) → False) ∨ False) → p2)) ∨ (p4 → (False ∨ p4)))) ∨ False) ∨ False) ∨ (p5 ∨ (False → p3))) ∨ (p5 ∧ p2)) := by
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
theorem thm_5_vars_190649530436989286834632927151 : (((p2 ∨ ((p5 ∨ p5) ∧ ((p1 ∨ True) ∨ p5))) → p2) ∨ ((p4 ∧ p2) → ((((p2 ∧ p1) ∧ True) → ((False ∨ False) ∧ (False ∧ p2))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651265866353211162696734273168 : ((((((p5 → p5) → False) ∧ ((((p2 ∧ p3) ∨ p2) ∨ p1) → ((p2 → p3) ∧ ((p4 ∧ (p5 → p3)) ∨ (p1 ∨ p2))))) ∧ (p3 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754248383378888015859902827712 : (((False ∧ ((False ∨ p3) ∧ ((((p3 ∨ False) ∨ ((p1 → p1) ∨ False)) ∨ ((False ∧ (p1 ∧ ((p2 ∨ p4) → (False ∧ True)))) ∨ p2)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178126036124735973323732529230 : ((((p5 → ((p2 ∧ (p4 ∨ True)) ∧ p2)) ∨ (p1 ∨ (True ∨ True))) → p1) ∨ (True ∨ ((True → ((p4 ∨ False) ∨ (p3 ∧ p1))) ∧ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345446696858046899618320117636 : (p3 → ((((p5 ∨ (False ∧ (p3 ∧ (p2 ∧ True)))) ∨ (((p1 ∨ (False ∧ p3)) → (p1 → (False ∧ (p5 → p3)))) ∨ p5)) ∨ (p5 ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211570047353060098991606974852 : (((p3 ∨ True) → (p2 → p2)) ∧ ((((((((p4 ∧ True) ∨ True) ∧ p2) ∨ p2) ∧ ((p4 ∨ True) ∧ p2)) ∧ False) ∨ ((p1 ∨ p2) ∨ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654927523478272839473717190180 : (((((((p4 ∧ ((True ∧ p2) ∧ p4)) ∨ p2) ∧ ((p3 → (p1 → (False ∨ (p5 ∨ p5)))) ∨ ((p1 ∨ p4) → True))) → p3) ∨ (False → p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56577421635335243830104617636 : (((False → (False ∧ (p2 ∧ p5))) → (((((False ∨ ((p4 ∧ ((p3 → p1) → p4)) ∨ ((p3 ∧ p3) → p1))) ∧ p4) → p2) ∨ p3) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340842946384134293383653589038 : (p2 → ((((p5 ∧ ((p3 → p4) ∨ (p4 ∨ p4))) ∧ (p2 ∧ (((((p2 → False) ∨ True) ∨ p5) ∧ p1) ∨ p2))) ∧ (p1 ∧ (p3 → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138405933165060504121738217489 : ((p5 → ((((True ∨ (p2 ∨ (p4 ∧ (p4 ∨ (p4 ∧ (p5 → (p3 → p5))))))) ∧ p2) → ((p3 ∧ p1) ∧ p2)) ∧ False)) ∨ (True ∨ (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372157164097329644986283789 : ((p1 ∨ (((p3 ∨ p3) ∨ ((((p3 ∨ (False → p5)) ∨ ((p4 ∨ (False → p4)) → p4)) ∧ (((True ∨ p2) ∨ p1) → p3)) ∧ p1)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300097965251339144117409491742 : (False ∨ ((((p2 ∧ p3) ∧ (((p5 → False) ∧ p1) ∨ ((p1 ∨ (False ∧ (p4 ∧ p1))) ∧ True))) ∧ ((p2 → (p4 → p1)) → p5)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134831273977221879716943914061 : (((p2 ∨ ((p1 → (((((True ∨ p2) ∧ (p5 ∨ (p4 ∧ (False ∧ p3)))) ∧ (p2 → False)) → p4) → p4)) ∨ False)) → p5) ∨ (True → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804678492611602624652029809843 : (((p3 → (((p5 ∨ p1) ∧ p1) ∧ (((p1 ∨ (p1 ∨ p2)) ∨ False) ∧ (p1 ∨ ((p3 → p2) → (p4 ∧ (p3 ∧ (p3 ∧ (p1 → False))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149776306761853918611111966207 : ((False ∨ ((((p3 ∧ p1) ∨ (((True ∨ True) ∨ p1) ∨ p5)) → (p4 ∧ (p3 ∧ ((True ∧ False) ∨ p1)))) → False)) ∨ (True ∨ (p3 ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64498020578396522606650249774 : ((p1 ∨ (((True ∧ (p1 → (((p5 ∧ True) ∨ True) → p2))) ∨ (True → ((p2 → p1) → p2))) → (p2 ∧ (((p4 ∨ p5) ∨ True) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341967572235540385705924057600 : (p2 → (((((((((p1 ∧ p1) ∨ p3) ∧ p3) ∨ p2) ∧ p5) → (((p5 ∨ p1) ∧ True) ∨ True)) → (p4 ∧ p1)) ∨ p1) ∨ ((p4 → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206464441995293983447929182603 : ((p4 ∨ (p1 ∨ ((p5 → p2) ∧ p5))) ∨ ((((p4 ∨ (True → p4)) ∨ True) → (p1 ∨ ((((True ∨ p2) → True) ∨ p2) → p3))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156274445625928069124299645603 : ((p4 ∨ (((p1 ∧ False) ∨ (p2 → (p4 ∨ p1))) ∨ (p3 → ((p3 → ((True ∧ p3) ∧ p3)) → p3)))) ∧ (((True ∨ True) ∨ True) ∨ (True ∧ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225522781086495135185414149963 : (((True → True) ∧ False) ∨ (((p4 ∧ (p2 → (p1 ∧ ((p2 ∧ p5) ∨ (p3 → False))))) ∨ ((p4 ∨ ((False → False) → False)) ∧ p3)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140255833490272635672458799913 : ((((True ∧ (((p1 ∨ ((True → p1) → p5)) → False) ∧ ((True → (p2 ∧ False)) ∧ p3))) ∧ p4) ∧ ((p2 ∧ p1) → False)) → (p1 ∨ (p2 ∧ True))) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257994710159884978505081889725 : ((p4 ∨ p1) → ((p2 ∧ (p3 → ((((p3 → (p1 ∧ p1)) ∨ (False ∧ (p1 ∧ False))) ∨ True) → p1))) → (((p4 ∨ (p3 ∧ p4)) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_304065019109794172040910694552 : (p1 ∨ ((p1 ∨ ((((p4 ∧ False) ∧ p3) ∧ p5) ∨ (((p5 ∨ p3) ∨ (p3 ∧ p1)) → (p3 → (p4 → (p5 ∨ (p1 → (p2 → p4)))))))) ∨ p5)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262161095857732147589827809234 : (True ∧ ((((p3 ∧ (p2 → p3)) → (((p5 ∨ ((p1 ∧ ((p5 → p5) → p2)) ∨ ((p1 ∨ p3) ∨ p2))) ∨ p1) ∨ (p4 ∨ p5))) ∨ True) ∨ p4)) := by
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
theorem thm_5_vars_64301462433244568670249257146 : ((False ∨ (p5 → ((((False → (True ∧ (True ∨ True))) ∧ (p4 → (((True → (p3 ∧ (True ∧ False))) ∨ p5) → (False ∧ p3)))) ∨ p2) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706931033640689422828855083352 : (((((((p2 ∧ p3) → (p3 → p1)) → p3) ∨ True) ∨ (p4 → (p5 ∨ (((p4 ∧ p4) → p5) ∧ (p1 ∧ ((p1 → p2) ∧ (p1 → False))))))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_255253636691777088097027230427 : ((p4 ∧ p5) → (((p5 → (p1 → (p5 → p2))) ∨ ((p3 → ((p1 → (p1 → (True ∨ p3))) → (False ∧ p2))) ∨ (p1 ∨ p2))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233696830732651896118860645540 : ((p2 ∨ (p3 → p4)) → (p3 ∨ ((((p5 ∧ (True → p2)) ∨ ((True → True) ∨ ((True ∨ p5) ∧ p5))) ∨ p4) ∨ ((True → (p3 ∧ p2)) → False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716446832267244110555965389689 : (((((True ∧ p1) ∨ (p5 ∧ p2)) ∧ (p5 ∨ (((True → p4) → (p1 ∨ (p2 ∧ True))) ∧ (p2 → (p4 → (((False → p1) → True) → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683252719531580653316145000899 : ((((p1 ∨ (((p4 ∨ ((p4 ∧ (p4 → p1)) → (False ∧ p1))) → ((p4 → True) ∧ p4)) ∧ True)) ∧ (False ∨ (((False → True) → p4) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256954133004669645032311298580 : ((p1 ∨ p5) → (((p2 → (p4 ∨ False)) ∨ ((p3 ∨ p5) → ((p4 → p5) ∧ ((True ∧ (p5 ∧ p3)) → ((p1 → p1) ∨ p4))))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



