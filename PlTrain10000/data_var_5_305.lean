variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201137259055845298612920279667 : ((False → ((True ∧ ((p3 ∨ True) ∨ False)) ∨ False)) → (((True ∨ (p1 → (((p5 ∨ p2) → (p1 ∨ p4)) ∧ p4))) → p5) ∨ ((True ∨ p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_317816515473988568751603438990 : (p4 ∨ (((((False ∧ False) ∨ True) → p2) ∧ (((((p5 ∨ p3) ∧ ((p5 → (p3 ∧ True)) ∧ (False ∧ (p2 → p5)))) ∨ p1) ∧ False) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123181518755202265129897309024 : (((p1 → (((p5 ∧ (p3 ∨ True)) → ((False ∧ True) ∧ ((p5 ∨ p5) → p2))) ∨ (p4 → (p2 ∨ p4)))) → ((p5 ∨ p5) ∧ False)) → (p2 → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (((p5 ∧ (p3 ∨ True)) → ((False ∧ True) ∧ ((p5 ∨ p5) → p2))) ∨ (p4 → (p2 ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589100417892015087506380656325 : (((((p4 → (((p1 ∨ (p4 ∧ (p1 → (p2 ∨ (p1 ∨ (p2 → ((p4 ∨ p4) ∧ True))))))) → p5) ∧ ((True ∨ p2) ∨ p2))) ∨ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149246047730600034707663330769 : (((p1 ∨ p1) ∨ ((p3 ∨ ((True → (p2 ∧ ((((p1 ∧ p3) ∨ True) → (p5 ∨ p1)) → False))) → p5)) → p2)) ∨ (p5 → ((True → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322387754851720158981217970398 : (p5 ∨ ((((p1 ∨ (True → (((p5 → ((True → p1) ∧ (p3 ∧ p5))) ∧ True) ∨ p5))) → True) → ((True ∧ (p5 → (True → p1))) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65721442222993716435800627038 : ((p4 ∨ (((((((p2 → (((p1 ∧ True) ∨ (p5 → False)) ∧ p3)) ∨ (p1 ∨ True)) ∨ p5) ∨ (p5 → p5)) ∧ p4) ∧ p3) → (p5 ∨ True))) ∨ p4) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1526632529923065849564542227 : (((p2 ∨ (p5 ∨ p5)) ∧ (p2 → ((p3 ∧ ((False ∨ p5) ∧ p2)) ∧ ((((p1 ∨ (p3 ∧ p1)) ∨ p3) ∧ True) ∨ True)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39006428474499267988640119049 : ((((p3 ∨ p3) ∧ ((((p5 → p4) → (p1 ∨ p1)) ∨ True) → ((((p4 ∨ ((True → p5) → p5)) → p4) → (p3 → p1)) ∧ False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47850461242273434578532782790 : ((((p5 ∨ (p5 ∨ (p2 ∨ ((p1 → ((p3 → (p3 ∧ (p3 → (p3 → (p3 ∧ False))))) ∨ (p5 ∧ p4))) ∧ False)))) → p1) → (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213622113883545879070476635075 : ((((p2 ∧ p5) ∨ p2) ∨ p2) ∨ ((p4 → (((p4 ∨ p2) → p2) ∧ (p3 ∨ ((p5 ∧ p2) → (p4 ∨ (p3 ∨ p3)))))) → (p2 ∨ (False → False)))) := by
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
theorem thm_5_vars_324553344070417113651751108113 : (p5 ∨ ((p5 ∧ ((p1 ∨ p5) → True)) → ((((((p3 ∨ p4) ∨ p2) ∨ True) ∨ ((p1 ∨ p1) ∨ False)) ∧ p3) ∨ (p4 ∨ (p1 ∨ (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_405609542853067259746409402424 : ((((((p5 → False) ∨ ((p3 ∨ ((p3 → (p1 → (p3 → p3))) → (p1 ∨ p2))) ∨ ((True ∧ True) ∨ ((True → p4) → True)))) → False) → p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → False) ∨ ((p3 ∨ ((p3 → (p1 → (p3 → p3))) → (p1 ∨ p2))) ∨ ((True ∧ True) ∨ ((True → p4) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355596363621874061108333888878 : (p5 → ((((p2 ∧ True) ∧ p2) ∧ (((p5 ∧ ((p1 → True) → True)) → p2) ∧ ((p4 ∧ False) ∨ (((False ∧ True) ∨ p5) → True)))) ∨ (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191476833291316365147492169828 : ((True ∧ ((p1 → ((False → p2) ∧ (p3 → p3))) → False)) ∨ ((True → False) ∨ (p1 → (False → ((((False → (p3 ∨ p2)) ∧ p3) ∨ p3) ∧ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1798283305645517224388399832 : (((p4 → (p1 ∨ p2)) ∨ (True → (p1 → ((((p2 ∧ (p3 ∨ (p5 → (p2 → p4)))) ∧ p3) → False) ∧ p3)))) ∨ ((True → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607506209842974415178615373432 : (((((True ∧ ((p2 → (((((p3 → False) → False) ∨ p5) ∧ p4) ∧ (((p4 ∧ True) → True) ∧ ((False ∧ p4) ∨ p4)))) ∧ True)) ∧ p4) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745699835908033655280176564670 : ((((True ∨ p4) → (p1 → ((True → p3) ∧ (p2 → (((p2 ∨ (p5 → False)) ∨ (True → p4)) → (p3 ∧ ((p3 ∧ (p2 → p1)) ∨ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37383563426141848187018244477 : ((((((((p2 → (True ∧ (p3 ∨ p5))) → (p5 ∨ p1)) → (p5 ∧ (p2 → p3))) ∧ ((p3 → p1) → (p4 ∨ p2))) → p5) ∨ p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41318181678424202460987151080 : (((((p2 → (p2 ∨ (False ∨ p4))) → ((p1 → p4) ∨ (p5 ∨ (p5 ∧ (p5 ∧ p3))))) ∧ (p4 ∨ (p4 ∨ (False ∨ (p4 → p1))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166659988251015786714082956093 : ((p1 → (False ∨ (p4 → ((p3 ∨ (p2 ∨ ((False ∧ p1) ∨ (p2 ∧ p4)))) ∧ (False → p3))))) ∨ (True ∨ (p1 ∨ ((False ∧ False) → (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304797849741428419163924865881 : (p1 ∨ ((((p5 → False) ∧ ((((False → p1) ∧ (False ∧ p2)) → ((p5 ∨ (True → (p4 → (p2 ∧ True)))) ∧ True)) ∨ p3)) ∧ p5) → (True → p4))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780283490134945203506253274274 : (((p2 ∨ (((((False ∨ (True ∧ (True ∨ (p5 ∧ False)))) ∨ p4) ∧ p4) ∨ ((True → p1) → (p1 → p3))) ∧ (((p1 ∧ False) ∧ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56102961021362232539471076475 : ((((True → False) ∧ (p4 ∧ p5)) ∨ (p3 ∨ (p5 ∨ (p2 → (((p4 ∧ p2) → ((True → p4) ∧ (p5 ∨ (p1 ∧ p3)))) → (p4 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804731648682472433688265999632 : (((p3 → (((p4 → p5) ∨ p2) ∨ ((p4 ∧ p5) → (p3 ∧ (((True ∨ p1) → p1) ∧ ((p1 ∨ p2) ∨ (True → (p5 ∧ (True ∧ p1))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137311948174873037241865919746 : ((p2 ∧ ((((True ∨ (True ∧ p1)) → (p1 → True)) ∨ (True ∧ True)) → (p2 → ((p5 ∨ p5) ∧ ((True ∧ p4) ∧ p5))))) ∨ ((p5 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39896910198250773910547169914 : (((p2 → (False ∨ ((p3 ∨ (p4 ∧ ((p5 → (((True ∨ False) → p1) → p5)) ∧ (((True ∧ p2) ∨ (True ∨ p1)) ∨ p3)))) → p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927568402639599786319037616532 : (((((((p2 → False) ∨ (p1 ∨ (p4 → p4))) ∨ p5) → False) ∧ (p5 ∧ ((p4 ∨ (p5 ∧ True)) ∨ (p3 ∧ (((True → False) → False) ∧ p2))))) → p1) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (((p2 → False) ∨ (p1 ∨ (p4 → p4))) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (((p2 → False) ∨ (p1 ∨ (p4 → p4))) ∨ p5) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (((p2 → False) ∨ (p1 ∨ (p4 → p4))) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184130904805996280889462816613 : (((p2 ∧ ((p5 ∧ ((p4 ∨ False) → (p3 ∨ p1))) ∧ p3)) ∨ False) ∨ (((p1 ∨ ((p3 ∨ ((False ∨ p4) ∨ p4)) ∧ p2)) → True) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338421896974190803992490073020 : (p1 → ((p4 ∧ (p2 ∨ (p2 ∨ p2))) → ((p5 ∨ ((p5 → p5) → ((p5 → ((p1 ∧ True) ∧ True)) ∧ p5))) ∨ (p4 ∨ (False ∨ (p1 → p1)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59312953778606547842342119747 : (((p4 ∨ p1) ∨ (((p4 → ((p1 → ((p3 → p2) → (p4 ∨ (p5 ∨ p3)))) ∧ p3)) → p2) → (p2 ∨ (((p1 ∧ p4) → p4) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218463648582955979144187999523 : (((p5 ∧ p3) → (p2 ∧ p5)) → (((p1 ∨ (((p1 → False) ∨ True) ∧ True)) ∨ (p3 → ((((p4 → p5) ∧ (p5 ∧ p5)) → False) ∨ False))) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173173594750855671079410754739 : ((p4 ∨ (((p1 ∧ (True ∨ ((p2 → (p4 ∨ p3)) ∧ p1))) ∧ p3) ∧ (p4 → p2))) ∨ (p1 ∨ ((p2 ∨ p4) ∨ ((p1 ∨ True) ∨ (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_37937733322771214931028492609 : ((((p1 ∨ ((p3 ∨ (False ∧ (True ∨ (p2 ∨ (p4 ∧ p1))))) ∨ (((p4 ∧ ((p4 ∨ p3) ∧ False)) ∨ False) ∨ p5))) ∧ (p1 ∨ p3)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622163111315442014091925193140 : ((((p2 ∧ ((False ∧ p4) ∧ ((p5 ∧ (p1 → True)) ∧ (((p5 ∨ ((p5 ∨ (p4 → (p2 ∨ p2))) ∨ p5)) → (p3 ∧ p5)) ∧ p3)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_115344561040583401761167562351 : (((p1 → (p4 ∨ (False → (((p3 → False) → p3) ∨ p3)))) → ((p5 → ((p1 ∧ (p5 ∧ p4)) ∨ p3)) ∨ (False → (p5 ∧ p3)))) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230335550524990922035278925049 : (((p2 ∨ p1) ∧ True) → ((((p3 ∧ p5) ∨ (p5 → False)) ∨ p1) ∨ ((p2 ∨ p1) ∨ (((p1 ∧ (True ∨ p2)) ∧ p2) → (False ∧ (p1 ∨ False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254803113280557541820585708900 : ((p3 ∧ p4) → (p5 ∨ ((p4 → (((True ∧ (p4 ∧ ((p2 ∨ p4) ∨ (True ∨ p2)))) → False) ∨ True)) ∨ (p5 → (p4 ∨ (p3 ∧ (False ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178942106918820739024911963389 : (((p2 ∧ p1) ∨ ((True → (p1 → p5)) → ((p4 → (p3 ∨ p5)) ∨ True))) ∨ ((((p4 → ((p2 ∨ False) ∨ (p3 ∨ False))) ∨ p1) ∨ True) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38727948190092576412619312439 : (((((p5 → p5) ∧ (p4 ∨ (p3 ∨ p5))) → ((((p2 ∨ False) ∧ False) ∧ ((p1 ∨ (p1 → (p3 ∨ p1))) ∧ (p2 → p4))) ∧ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136990612998618691556351232020 : (((p5 ∧ p2) → ((True ∧ ((p5 ∧ p1) ∨ p2)) → (p3 ∨ (((p2 → p2) ∨ ((True → p2) ∧ (False ∨ True))) ∧ p3)))) ∨ ((p1 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40028449205976709247772856014 : ((((((p4 ∧ (p5 → ((((p1 → ((p4 ∧ p3) → p3)) ∧ ((p3 → False) ∧ (p5 ∧ p1))) ∧ p2) → p4))) → p5) ∧ True) ∧ p2) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4298587833837185492153758308 : (True → ((p4 → (p1 ∨ p5)) → ((((p5 → (p2 → False)) → (p2 ∧ p3)) ∨ (p3 ∨ True)) ∨ ((((True ∧ True) ∧ True) ∧ p5) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68093207825754910697598619759 : ((p2 → (True → (((((((True ∨ (p3 ∨ (p1 ∨ p4))) → p4) → (((p5 ∧ p5) → True) → p4)) ∧ True) → (p3 → p2)) → p4) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725316355566500819719766153412 : ((((p3 → (p2 → False)) ∧ (p5 → (((p4 → (p1 ∨ p2)) ∧ (((p1 ∨ (False ∨ (False ∧ (p2 → p3)))) ∧ p2) ∨ True)) ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255581588586724707519038490876 : ((p5 ∧ p3) → ((p3 → p1) → (((False ∨ ((p2 → False) ∧ (p1 → ((p4 → p2) → (((False ∧ True) ∧ p3) ∧ (True ∨ p4)))))) ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46202274314626780603749768272 : ((((p3 → (False ∧ ((((p2 ∧ True) ∨ (False ∨ ((p3 → (p2 → (False → p2))) ∨ (True → True)))) → True) ∧ p4))) → p3) ∧ (p1 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166822371359469440645029905339 : (((((((p2 ∧ (p5 ∧ p4)) ∨ (p4 ∨ ((False ∨ False) ∧ True))) ∨ p5) → p2) ∨ p5) ∧ True) → ((True ∨ p1) → (True → ((p3 ∧ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
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
theorem thm_5_vars_309929436069064365819125048869 : (p2 ∨ (((p2 ∧ (p3 ∧ p2)) ∧ (False ∨ (((p3 ∨ p1) ∨ (p5 ∧ p2)) ∨ ((p1 ∧ p1) → p1)))) ∨ ((True ∧ (False ∨ p5)) → (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694611497817470716014842334493 : ((((p4 ∧ (p4 ∨ (((p2 → (p1 → (True ∨ p3))) → (True → p4)) ∨ p4))) ∨ (True ∨ (p5 → (p5 → (p2 → (p3 ∧ (p2 ∨ False))))))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_61532382970965795416159680027 : ((p1 ∧ (((p5 → (p4 ∧ True)) ∧ ((p2 ∨ p4) → (p2 ∨ ((p4 ∧ p5) ∧ False)))) → ((p5 → ((p3 ∧ p1) → (p2 ∧ p2))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134541317522675606823458921496 : ((((((((p1 ∧ ((p4 ∧ True) ∧ False)) ∧ p3) ∧ True) ∧ (False ∨ p4)) ∧ ((True ∧ (p4 ∨ p4)) ∧ p1)) → p2) → False) ∨ ((False ∧ p1) → p4)) := by
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
theorem thm_5_vars_548403549849585627236144582 : (((((p1 ∧ p1) → (p5 ∧ p3)) ∧ ((False ∨ ((((p5 ∨ p5) → p3) ∨ True) ∧ (p5 ∨ ((p1 ∨ p2) ∨ p1)))) ∧ False)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51943762059104154201919988171 : ((((p2 → (((False → p5) ∨ p3) ∨ (False → p2))) → (p3 → (p1 ∨ (False ∨ p1)))) ∨ ((((True → p2) ∧ p3) ∧ p4) ∧ (False → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147112732699787086049408890479 : ((((p4 ∨ p1) ∧ ((p3 ∨ p3) → ((((p3 ∨ p2) ∧ (p5 ∧ (False ∨ p5))) ∧ True) ∨ (p2 ∧ p3)))) ∧ False) ∨ (((False ∨ p1) → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_164875006343842442226623174771 : (((True → (False ∧ (((p2 ∧ p1) → False) → (p4 ∨ (p3 ∨ ((False → p1) ∧ p2)))))) ∨ True) ∨ (p2 ∧ ((False → p5) → (p3 ∨ (p3 → p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693871017531291857503193392018 : (((((True ∨ (((p4 ∧ p4) ∧ (p5 ∧ p4)) → ((p4 → p5) → p1))) → p1) ∨ ((p1 ∨ (p3 → ((True ∨ True) ∧ (p5 → True)))) ∧ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339882761682394627693838445275 : (p1 → (True → (True ∧ ((p5 → True) → ((((p3 ∧ (((p2 → True) → (p3 ∧ (p5 → ((p1 → p5) ∨ p4)))) ∧ p4)) ∨ p5) ∧ p1) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805294511999486692583229427136 : (((p3 → (p5 ∧ (((False ∨ (p1 → p5)) ∧ p2) ∧ (((((((p1 ∨ ((p3 ∧ p3) ∧ False)) ∨ p3) ∧ p3) → p4) → p2) → p3) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200108422172383662791431727197 : (((p2 ∧ (p1 ∨ p3)) ∧ (False → (p2 ∨ p3))) → (((True ∧ ((False ∧ p2) ∨ (p5 ∨ (p5 ∨ ((p4 ∨ p4) → p1))))) ∨ True) ∨ (False → p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234697514482960086452786380481 : ((p4 → (True ∨ p4)) → ((p3 → ((p5 → p1) → p4)) ∨ ((p2 → ((p2 ∧ p5) ∨ ((((False ∧ p1) ∨ p3) → p4) → False))) ∨ (True ∨ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243779471103941760652518090188 : ((p5 → p5) ∧ (((p3 ∧ p4) → ((((False ∧ ((p3 → True) → p1)) → ((True ∨ p3) ∧ p3)) → (False ∨ p2)) ∧ p1)) ∨ (p3 → (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134162494274039039209002251192 : ((((p4 → ((((True ∧ ((False ∧ True) ∧ ((p5 ∧ p3) → p4))) → True) → p5) ∧ p3)) → ((p1 ∧ True) ∧ p5)) ∨ p5) ∨ (False → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41837382019811322530386971548 : ((((p5 ∧ (False → p4)) ∧ (p2 ∨ (((p1 → ((True ∧ p5) ∨ p2)) ∧ True) ∨ (p4 ∨ ((False → ((p5 ∨ p1) ∨ p4)) ∧ p5))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110918263411309513384434966140 : ((((p4 ∨ (((p5 → (p5 → False)) ∧ (p1 → (p2 ∨ ((p4 → p1) ∨ ((p3 ∨ p5) ∧ False))))) ∧ (p1 → p5))) → p4) ∧ True) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184224639692579469978581382815 : (((((p3 ∨ p1) → (p1 ∨ (p5 ∨ (p3 ∨ p4)))) ∨ False) → False) ∨ (p2 ∨ ((p3 ∧ (p3 → True)) → (p3 ∨ ((p2 → True) ∨ (p1 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68296771743199790150160940531 : ((p3 → ((((p1 ∨ (((p5 ∧ p1) ∧ (((p1 ∨ p1) → p1) ∧ ((p1 ∨ p4) ∨ True))) → p1)) ∧ False) → p4) → ((p2 ∧ p2) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64339117103426593746814274996 : ((p1 ∨ ((p1 ∨ ((True → (((p2 → (p2 ∨ ((p2 ∨ True) ∧ ((p4 ∧ p3) ∨ (p5 → (p3 → p1)))))) → p1) ∨ p5)) ∨ p1)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709851431901851864647861690551 : ((((p4 → (p1 ∨ ((p3 → (p5 ∧ p4)) ∨ p4))) → (p3 → (p3 ∧ ((((p1 → (True → ((p5 ∧ True) → False))) ∧ p2) ∨ p4) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65309342427375526752582116373 : ((p3 ∨ (((((((p5 → p1) ∧ p5) ∨ (False ∨ p3)) → (p3 → p4)) ∧ (p2 ∧ (True ∧ False))) ∨ (p3 ∨ True)) ∧ ((False → p2) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146903116511915421911565588024 : (((((p2 ∧ ((((((p1 → (False ∧ (True ∧ True))) ∨ p5) ∨ False) ∧ p2) ∧ p2) → p5)) ∧ True) ∧ p2) ∧ p5) ∨ ((p3 → (p3 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382382279329474431276610450340 : ((((((((p4 ∨ p1) ∧ (p1 ∧ ((p2 ∨ True) → False))) ∨ ((p5 ∧ False) ∧ p5)) ∨ (((False → p3) ∨ p4) ∧ (p3 ∨ p4))) ∨ True) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322521350655663104963461372243 : (p5 ∨ ((p2 ∧ ((((p4 → ((p4 ∧ (p3 → (p1 → ((p5 ∧ (p3 → False)) ∨ (True ∨ True))))) → (False ∨ True))) ∨ p5) ∨ p5) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147086217859804515422433848448 : ((((p2 ∧ (p1 ∨ (p4 ∨ False))) ∨ (p4 → ((p3 ∧ (p2 ∧ ((True ∧ True) → (p4 → p1)))) → p5))) ∧ p5) ∨ (p1 ∨ (p2 ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_156606077002893500048724002770 : (((((True → (False ∨ p3)) ∧ ((True → ((p5 ∨ p3) ∧ (p1 ∨ (p3 ∧ True)))) ∨ p2)) ∧ p2) ∧ False) ∨ ((((p2 ∧ False) ∧ p1) ∧ False) → p4)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148520535763568282963909453690 : ((((p2 ∨ (p5 → ((p2 ∧ (p4 → (p3 ∨ p5))) ∨ p1))) → False) → (p5 → (p5 → ((p4 ∨ p1) → p3)))) ∨ ((p1 ∧ (False ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707599915059265529312294054576 : (((((p1 ∨ p1) ∧ (True ∧ (p3 ∧ (p1 ∨ p5)))) ∨ (((True ∨ p1) ∨ (((p2 → ((p2 → False) ∨ True)) ∨ p5) ∨ (True → p1))) ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46448280033770655002604875443 : (((((p4 ∧ (p5 ∨ True)) ∧ p3) ∨ (p3 ∧ ((p3 ∨ (((((p5 ∨ False) ∧ True) ∨ p1) → p2) ∧ p3)) → (p5 → True)))) ∧ (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201095501100521934208883406800 : ((True → ((False ∧ ((True ∨ p2) ∧ p3)) ∧ p1)) → (p2 ∨ (p1 ∧ ((p1 ∨ ((((False → True) ∨ p5) → False) → False)) → (p2 ∨ (True → p1)))))) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64974393730612481893292352852 : ((p2 ∨ ((((p3 ∧ p2) → p5) → p1) ∧ ((p2 ∧ (p1 → p5)) ∧ (((p4 ∧ False) ∨ ((p1 ∧ p1) → (p2 ∨ (p4 ∨ p1)))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64428048314454071204195339899 : ((p1 ∨ (((p5 → (False ∨ (((((p2 → (p2 ∧ (p2 ∨ True))) ∧ p4) ∨ p1) → (p2 ∨ p1)) → p2))) → (p1 ∧ p1)) ∧ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246058065120393442726165441947 : ((p4 ∧ False) ∨ (p5 ∨ ((p1 → (((p5 → (p5 → (p1 ∧ (p5 → True)))) ∨ p1) ∧ p1)) → ((p5 → (False ∨ p4)) ∨ (False → (p5 ∨ False)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219542340286631199436537579191 : ((p5 ∨ (p2 → (p5 ∧ False))) → ((p4 → p4) → ((((True ∨ p4) → True) → (p1 ∧ ((False ∧ p3) → False))) → (p1 → ((p1 ∨ True) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789604955511394050035358487689 : (((p5 ∨ ((((p4 ∨ True) ∧ (p3 ∨ (p1 → False))) ∧ True) → ((p4 ∨ (((p4 → (p3 ∧ False)) ∧ ((p1 → False) ∨ True)) ∨ p4)) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119250472927344845571824529079 : ((p2 → (p1 ∨ (((True ∧ (p1 ∧ True)) ∨ ((p4 → (((p1 → p5) → (p4 → False)) ∨ p2)) ∨ (False ∧ p3))) ∨ (p5 → p1)))) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458314282215261117291492514647 : (((((p1 → True) → (((((False ∨ (p2 ∨ p5)) ∧ (p1 ∨ False)) ∨ False) ∨ p4) ∨ (True ∨ p4))) ∨ ((p5 → (p5 → p1)) ∧ (p1 → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206447633191359942083988506473 : ((p4 ∨ ((p3 ∧ p3) ∧ (p3 ∨ p3))) ∨ (True ∨ (((p1 ∨ (p5 ∧ (False ∨ (True ∨ (((p5 ∧ (True → False)) → True) → p1))))) → p2) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760555874990034886624435275044 : (((p2 ∧ (p2 ∧ (p3 → (((False → (True ∧ ((p2 → (True ∨ (p3 → ((p4 ∧ False) ∨ p1)))) ∨ (False ∧ p1)))) ∧ True) → (True ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778046655237891051249284431580 : (((p1 ∨ ((p5 ∧ p2) ∧ (((p5 → p1) → (((False ∨ (p5 ∨ ((False ∧ p3) ∨ ((p2 ∨ p2) ∧ False)))) ∧ p1) ∧ (p1 → p1))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218851923086220632164546941693 : ((p2 ∧ ((p2 → p1) → p3)) → (((((((p4 ∨ (False → p3)) ∨ (p2 ∨ p5)) → (p4 → p5)) → (p3 ∨ p2)) ∨ p1) → (True → p5)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((((p4 ∨ (False → p3)) ∨ (p2 ∨ p5)) → (p4 → p5)) → (p3 ∨ p2)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42129637172376012214728560739 : ((((p1 ∨ p4) → ((p4 ∧ (p2 ∨ (p1 ∨ ((True ∨ True) → p1)))) ∧ (p2 ∧ ((True ∧ (((p3 → p1) ∧ False) ∨ p5)) ∨ False)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115225485160650292059358286154 : (((((p1 → ((p5 → p1) ∧ True)) → (p3 ∧ p3)) ∧ p3) ∨ (p3 ∧ ((p1 → p3) → ((p4 ∨ p2) → (p2 ∨ (p5 ∧ p5)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55329613227796028310885266221 : (((p4 ∨ ((p1 ∧ (p1 ∨ p2)) ∨ p4)) ∨ (False ∧ ((((((False → p3) ∨ p2) ∨ p5) ∨ (p1 ∨ True)) ∨ p4) ∧ (p5 ∧ (p5 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717974441701018657081600560922 : ((((((False ∧ p2) ∧ p5) ∨ p4) ∨ (True ∧ (((((p5 ∨ ((p3 → p2) → (p1 → p2))) ∧ p4) ∧ (p3 → p4)) ∨ (p3 ∨ True)) ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_195507452178235581235838669587 : ((((p3 ∧ False) ∧ p3) → (True → (True ∧ p3))) ∧ (((p1 ∧ (p4 ∧ p5)) ∨ p4) ∨ (p1 ∨ ((p4 ∧ p1) → ((p5 ∧ (True ∧ p3)) → p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h7.left
  let h14 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684451107617311386927257853968 : ((((((p1 → ((True ∨ False) → (p4 ∧ True))) ∧ p1) → ((False ∧ ((p1 ∨ p4) ∧ p5)) ∧ p3)) ∨ ((((p3 ∧ p5) ∧ p1) → p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344164254494341770367041871949 : (p2 → (p1 ∨ (((False ∧ ((((((p5 ∧ (((p1 → p3) ∨ p1) ∨ (p3 → p4))) ∧ p1) ∨ p3) ∨ True) ∧ (p4 ∧ p5)) ∧ True)) ∨ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42512830588166048976425110931 : (((False ∨ ((p1 → p5) ∨ (p3 ∨ ((p5 ∨ (((p3 ∧ (p5 → p5)) ∧ p4) ∧ (p4 ∧ (((p3 ∨ p2) → p5) ∧ p3)))) ∨ True)))) ∨ p1) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617314013077580108420885751346 : ((((((True ∨ (p5 ∧ (p4 → (True ∨ p4)))) ∨ p4) → ((((((p2 ∨ p3) → p1) → p5) ∧ (p5 → (p4 ∨ p4))) ∨ False) ∨ True)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_797241372817829970230983279252 : (((p1 → ((((True → (p3 → ((True ∨ p4) ∧ ((((p3 → (p2 ∧ ((p4 ∨ True) → p3))) ∨ p1) ∨ True) → False)))) ∨ p2) ∨ True) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



