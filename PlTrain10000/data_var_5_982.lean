variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307315531749291676012246466294 : (p1 ∨ (p3 ∨ ((((False → p4) ∧ (p4 ∨ (False ∧ ((p1 ∨ p4) ∧ (True ∨ p1))))) ∧ (p5 ∧ (((p1 → False) → False) ∧ p3))) → (p4 ∨ False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49376723142595253836463987072 : (((p5 → ((p1 ∨ False) ∨ (((p1 ∨ p2) ∨ (p4 → ((True → True) ∨ p2))) → (((p3 ∧ p4) ∨ p5) ∧ p5)))) ∨ ((True → True) → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319649273499972555884844164025 : (p4 ∨ ((p2 ∧ ((((p4 → p1) ∨ p3) → False) ∧ p1)) ∨ (True ∧ ((((p2 ∨ p3) → (p5 ∧ ((p5 ∨ p4) ∧ (True ∧ p5)))) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_38937666321623704385677671332 : (((((False ∨ p5) → p4) → (p4 ∨ ((p4 → ((((True ∨ p5) ∨ (False ∧ (p4 → (p1 ∨ False)))) ∨ p1) → (p5 ∨ True))) ∧ True))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250151842449205044621336219503 : ((True → p5) ∨ (((p2 ∧ ((p3 ∧ p2) ∨ (True → (p4 ∧ (((p1 → p3) → True) ∧ (p4 ∧ ((p3 → p3) ∨ p4))))))) → p1) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347633478049714804542166938937 : (p3 → ((p4 → ((p1 → p5) → False)) ∨ ((p1 ∧ False) ∨ ((p1 → True) ∨ (False ∨ ((((p1 → ((p2 ∨ p5) → False)) ∨ p2) → p2) ∧ p3)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111710125032459352037186862923 : (((((p3 → (p5 → ((((p4 ∧ (p2 ∨ p2)) → p4) ∨ (p4 ∧ p4)) ∧ p5))) ∨ ((False ∨ (p4 → False)) ∨ p5)) → p2) ∨ True) ∨ (p3 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319576420603392827515609824602 : (p4 ∨ ((((True → (False ∧ p4)) ∧ p2) ∧ (p3 → (True ∨ p3))) → (True → (((p1 ∨ (((p2 ∨ p1) ∧ p1) ∨ (True → p1))) → p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124625165592780979797728128400 : (((p4 → (((p1 → False) ∧ True) ∧ p3)) ∨ (((True ∧ (True ∧ (p3 ∨ p3))) → (p4 ∧ (p5 ∧ p5))) → (p2 ∨ (p4 → p3)))) → (p5 ∨ True)) := by
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
theorem thm_5_vars_53846629559592688153768263045 : (((((p3 → p3) → (p2 ∨ False)) → (p4 ∧ (False ∨ p3))) ∨ (((True ∧ (p4 → p3)) ∧ (True ∨ p4)) ∨ ((p1 → (p5 → p1)) ∨ p1))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178594097639508383753496362605 : (((((p5 → p2) ∨ False) ∧ (p2 ∧ p3)) ∨ ((p5 ∨ (p5 ∧ p1)) ∨ p2)) ∨ (p5 ∨ ((((p1 ∧ (p3 ∧ p3)) ∨ False) → (p2 → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116281991249275215273865112751 : (((p1 ∨ (False ∨ False)) ∨ (((p4 ∨ ((False → ((p1 ∧ (p5 → p5)) ∧ p5)) → (p4 ∧ (p1 ∨ p3)))) ∨ p2) ∧ (p1 → True))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192302053005249955712681859780 : (((True ∧ (p4 ∧ ((p4 ∧ False) ∨ (p5 → p4)))) ∧ p1) → (((((((True ∧ False) ∨ p4) ∧ p4) ∧ p5) ∨ (False ∧ p3)) ∧ (False ∨ p5)) ∨ True)) := by
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
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135379386231560193746244597551 : ((((p4 ∨ (((((p1 ∨ (True ∧ p1)) → (p5 → (p5 ∨ p1))) ∧ p5) ∨ p4) ∨ p5)) ∨ p3) ∨ ((True ∨ True) → p4)) ∨ ((p2 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612618729259035899309161769125 : (((((((p2 ∨ p2) → (((p3 → False) ∨ p2) → (p4 ∧ (((False ∨ True) → (p2 ∧ p4)) ∨ p2)))) ∨ (p5 ∨ p2)) ∨ (False → p5)) ∨ False) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670768222887589529571708360374 : ((((False ∧ (((True ∨ p4) ∧ p4) ∧ (((((True ∨ p2) ∨ p5) ∧ p5) → ((p1 ∨ p2) ∨ p2)) ∨ (p2 ∨ p5)))) ∨ (True ∨ (p1 → p2))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_227312689463252023949831071136 : (((p2 → p2) → p2) ∨ (((False → ((False → (p4 ∨ p1)) ∨ (p3 → p1))) ∨ False) → ((p3 ∧ ((p5 ∨ p5) ∨ (p1 ∨ p4))) → (p1 ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49980782857769855526038570141 : (((((True → p4) → ((((p4 ∧ False) ∨ p1) ∧ (p3 ∧ p2)) ∧ True)) ∧ (((p4 → True) ∨ p5) → p4)) ∧ ((p2 → (True ∨ p2)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349232766874311575860578025635 : (p3 → (p1 → (((p5 ∧ (p2 → (p3 ∧ (((p5 → True) → p3) → False)))) ∧ ((p1 ∧ p1) → False)) ∨ (((p5 → False) ∨ p4) → (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254209356626587255577665810209 : ((p2 ∧ p2) → (((p5 ∨ (((p5 ∧ p5) ∧ (p1 ∧ (p2 ∧ p2))) ∧ (((True ∨ ((p2 ∨ p3) ∧ p4)) ∨ p2) ∨ p2))) ∨ (p1 ∨ p1)) ∨ p2)) := by
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
theorem thm_5_vars_190940685398298009408308781376 : ((((p4 ∧ p2) ∨ (p1 ∨ p5)) ∧ (p4 → (True → p1))) ∨ ((p5 ∧ p5) ∨ ((p2 → p1) ∨ ((True → ((p2 ∧ False) ∧ (True ∨ True))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608721696133411600722212769693 : (((((((False → p1) → (((p1 ∨ p4) ∧ (p3 ∧ ((p1 ∧ ((p5 ∧ (p4 ∨ False)) ∨ p4)) ∧ p2))) ∧ p5)) → (p4 ∧ p4)) ∨ p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214748027770521145208329493134 : (((p4 ∧ p2) ∨ (p4 ∧ p3)) ∨ (p2 ∨ ((True ∧ (False ∨ ((p4 ∨ p1) → p2))) → (p5 → (p2 → (p1 → (((True ∨ False) ∧ p4) → p4))))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145218426095162417782274173291 : (((p3 ∧ ((((True → p4) ∧ p1) ∧ p2) ∨ p5)) ∨ (p1 → ((False ∨ (p2 → (True ∧ True))) ∨ (False ∧ p3)))) ∧ ((p5 → True) ∨ (p1 ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254892892440836009593772436604 : ((p4 ∧ True) → (((p2 ∨ ((p3 → False) ∧ p4)) ∨ ((p5 ∧ ((((True ∨ p2) ∨ False) ∧ p4) → (True ∧ p5))) ∨ True)) ∨ (p5 ∧ (p2 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148112427035776111615249073442 : (((((p1 ∨ ((p3 ∧ p3) → (p2 ∧ p5))) ∧ p1) ∧ ((False → True) ∨ (p2 ∨ (True → True)))) → (False ∨ p4)) ∨ (True → ((p1 ∧ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64627209454226506844708313327 : ((p1 ∨ (p1 ∧ (((p1 ∧ (p2 ∨ (p3 → (p3 → p5)))) → True) → ((True ∧ p4) ∧ (False ∧ (True → (p5 ∧ ((p2 ∨ True) ∧ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241725104515924585227141318891 : ((p1 → True) ∧ ((((True ∧ (True ∧ p5)) ∨ p3) ∧ True) ∨ ((((p3 ∧ p5) ∨ (p5 → (True → (p4 ∨ ((p5 ∧ p3) ∧ True))))) ∨ False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90879611187265447352034707073 : (((p5 ∨ False) ∧ ((((p4 → (False ∧ (p5 ∧ (p5 → p2)))) ∧ (p4 ∧ (True → p4))) ∧ (False ∨ ((p5 → p3) → (p3 → True)))) ∨ False)) → False) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116334365151921189683029563384 : ((((False → p3) ∧ p1) → ((p2 → (p3 → (((p4 → p1) ∧ True) ∧ (((False ∧ False) → ((False → p2) → False)) → p4)))) ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142197177908898306341777283828 : ((p1 ∧ ((((False → (((False ∨ (p1 ∧ p4)) ∧ False) ∧ True)) ∧ p1) → ((p1 → p4) ∧ p3)) ∧ (p2 → (p4 → False)))) → (p3 ∧ (p3 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((False → (((False ∨ (p1 ∧ p4)) ∧ False) ∧ True)) ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : ((False → (((False ∨ (p1 ∧ p4)) ∧ False) ∧ True)) ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- False on the left can always be used.
    apply False.elim h15
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h14
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327031304951251141126573519918 : (True → (((p5 ∧ ((p1 ∧ (p5 ∧ ((p3 ∧ p3) ∨ (False ∨ p5)))) → p3)) → (((p1 ∨ p3) ∨ p5) ∧ (((p2 ∧ p1) ∨ p1) ∨ True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117518971157401524292390766428 : ((p2 ∧ ((p1 → ((p4 ∧ True) ∨ ((True → ((p3 ∨ (False → (p1 → p2))) ∧ (False → (True → p5)))) → (p3 ∧ p4)))) ∨ False)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245426089120298384365602601267 : ((p2 ∧ p4) ∨ (((False ∨ ((p1 → False) ∧ (p3 → ((False → False) ∧ p5)))) ∨ p4) → ((p2 ∨ p1) ∨ (p1 ∨ ((p2 ∧ p1) → (p5 ∨ p4)))))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613154117549750316557573685710 : ((((((((False ∨ (((True ∨ p3) → True) ∨ ((p2 ∧ p4) ∨ True))) ∧ p1) ∧ ((p4 → p5) ∨ p1)) ∨ (p4 ∨ p3)) → (p1 → False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214418848028322085530538520280 : (((p2 → (p4 ∨ p3)) → False) ∨ ((((p3 ∨ (((True ∨ True) ∨ (p2 ∧ True)) ∨ False)) ∧ True) → (((True ∧ p5) ∨ p3) ∨ (False ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638654795589580772771024907490 : (((((((False → False) ∨ (p2 → True)) ∨ p3) → (((((False ∨ (False → p5)) ∧ p2) → p5) ∨ ((p4 → False) ∧ False)) → (True ∧ p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69165895294817801598467446829 : ((p5 → (((((p4 ∧ p1) → p3) → ((((p3 ∧ False) ∧ True) → p5) → (p4 → p2))) ∨ p5) ∧ (p2 ∨ (True → (p3 ∨ (p5 ∧ True)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54129093783522484489594817737 : (((p2 ∨ ((p5 ∧ (p4 ∧ ((p1 → p1) → False))) ∧ p3)) → (p1 → (False ∨ (((False ∧ p3) ∧ p2) ∨ ((True ∨ p2) ∨ (p1 → p1)))))) ∨ p2) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
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
theorem thm_5_vars_740373316653542447604846032776 : ((((p1 ∨ p2) ∨ ((p4 ∧ (p4 ∧ True)) ∨ (((True → (((p1 → ((False ∨ p2) → True)) ∧ p2) ∧ (p3 → True))) → (p3 → p5)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731838711953624810601803759176 : ((((p4 → (True ∨ p3)) → ((True → p4) ∨ ((p1 ∨ (False → p3)) ∧ ((True ∨ ((p1 → True) ∧ (p3 → False))) ∨ (p4 ∨ (False ∨ p5)))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115360794441291047195852793103 : ((((True ∧ (True ∨ ((p3 ∧ p5) → p4))) ∨ p1) ∧ (((p4 ∧ p1) → (p4 → False)) ∨ (((False → p1) ∨ (p2 → False)) → p3))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171943473471621557368591032905 : ((((p2 ∨ (p1 ∧ (((p4 → p3) ∧ True) → p2))) ∧ (p4 ∧ p1)) ∧ (p4 → p3)) ∨ ((((p2 → False) ∨ (p2 → p2)) ∨ (p1 → True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133702323333002093720601089672 : ((((((p4 ∨ p3) ∧ (False → (False ∧ p3))) ∨ (p3 ∨ ((p5 ∧ p5) → p4))) ∧ ((p3 ∨ p4) ∨ (False ∧ p3))) ∧ p2) ∨ ((p3 ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655688605464524493433997123734 : ((((((p5 ∧ (p4 → (p5 ∨ p3))) ∨ ((p4 → False) ∧ (True ∧ (False ∨ ((p2 → p1) ∨ False))))) ∧ (True ∨ (False ∨ p5))) ∨ (p2 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246071883558325793024278558462 : ((p4 ∧ p1) ∨ ((((p1 ∨ False) ∨ ((p2 ∨ True) ∨ ((p4 ∨ (p1 ∧ True)) ∧ (((p1 ∨ p5) ∧ p4) → p5)))) ∨ (p2 ∨ (p1 → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216860732952354162324211999995 : (((False ∨ (p2 ∧ p1)) ∧ p2) → ((p1 ∧ True) ∧ (((p5 ∧ True) ∧ ((p3 ∧ ((p2 ∧ p5) ∧ p4)) ∨ (p5 ∧ p5))) ∨ (p4 → (p2 ∧ p1))))) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304019949100657698529458279813 : (p1 ∨ ((False ∧ (((p1 → p1) ∧ (True ∧ (p5 ∨ p1))) → (p2 ∨ ((False ∨ (p1 ∧ p5)) ∧ (((p4 → True) ∧ p5) ∨ (False → p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41871197935988654235505606701 : (((((p4 ∨ p5) → p4) ∨ ((p3 → p3) → (((p5 ∨ False) ∧ ((p5 → ((p5 ∧ p4) → p2)) ∨ p5)) → (True → (p2 ∨ p3))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656353731937547857669131006093 : ((((((p4 ∧ (p3 → (p5 ∧ (p4 ∨ ((p5 ∨ False) ∨ p3))))) → True) → ((p4 ∧ ((p2 ∧ True) → (p3 → p2))) → False)) ∨ (p5 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337665632426895690342536831216 : (p1 → (((((True ∨ p5) → p2) ∨ (p2 → p5)) → (((p4 ∨ (p5 ∧ p3)) → (p5 ∧ False)) ∨ False)) ∨ (((p5 → (p2 → p1)) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65592811909955912594391484161 : ((p4 ∨ ((((((p5 ∧ p1) ∨ False) ∧ (True ∧ (p2 ∨ p3))) ∧ ((p2 → ((True ∨ (p4 ∧ p4)) ∧ p5)) ∧ True)) ∧ (False ∨ p4)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765386819119212996530995363382 : (((p4 ∧ ((p5 ∨ (p4 ∨ (((p3 ∨ p2) ∨ ((p5 → p2) → p1)) ∨ (p3 ∨ (p2 ∨ ((p3 ∨ p4) → True)))))) → (p1 ∧ (False ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312731783185199181303453728915 : (p3 ∨ ((((((p3 ∧ (False → True)) ∨ ((p5 → p5) → p3)) → p3) ∧ p2) ∨ (((p3 → (p3 ∧ p4)) ∧ p2) ∨ (p1 ∨ (p3 → p3)))) ∧ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325943994462833004815623072783 : (p5 ∨ (p5 ∨ (((p2 ∧ p2) → (False ∨ p3)) ∨ (((False → False) → (p2 ∧ p3)) → (p2 ∨ ((p3 ∧ ((p3 → p4) ∨ p1)) ∧ (p3 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50460586044902234419936588486 : (((p5 ∨ ((p5 → (((p3 ∧ (p4 ∨ ((p5 → p2) ∨ p3))) ∧ (p1 → p2)) → (p4 ∨ False))) ∧ p2)) ∨ (True ∨ ((p5 → p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327172020089157085944240719808 : (True → ((False ∨ (((False ∨ (((False → p5) ∧ ((((p4 → False) ∧ (True ∧ p1)) ∧ ((True → p1) ∨ p3)) → p2)) ∧ p3)) ∨ True) ∨ p3)) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2939283568384071616490441876 : (((p2 ∨ p2) ∨ p2) ∨ (((((p4 → (p4 ∧ p2)) ∨ (p2 ∧ True)) ∧ p5) ∧ (p2 ∧ (False ∧ (((p4 → False) ∨ False) ∧ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244075599180125403574873015394 : ((True ∧ p3) ∨ ((p2 ∧ (p4 ∧ ((((p4 ∧ (p1 ∨ ((p3 ∨ p5) ∨ ((p2 ∧ p3) ∨ (p4 → True))))) ∧ True) ∨ p2) → (p1 ∧ p3)))) → p3)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 ∧ (p1 ∨ ((p3 ∨ p5) ∨ ((p2 ∧ p3) ∨ (p4 → True))))) ∧ True) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260666587423549506414930088204 : ((p3 → p3) → (((p5 ∧ ((False → (((p1 ∧ (p5 → p3)) → p4) ∧ p1)) ∨ p5)) ∧ (p1 ∧ p3)) → ((p4 ∧ ((False → p1) ∨ p1)) → p4))) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h2.left
    let h19 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h19.left
      let h24 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215281978723333360558278375112 : ((False ∧ (p5 → (False ∨ p1))) ∨ (p2 → (((((p5 → (p2 ∧ p2)) ∨ p3) ∨ (True ∧ p3)) → True) → ((((True → p1) ∨ True) ∧ p2) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620612485560989044769614113572 : (((((p5 → p4) ∨ (((True ∨ True) ∧ ((p1 ∨ (p2 ∨ (p1 ∧ (True ∨ ((p4 → (p2 ∧ p3)) ∨ (p5 ∨ p3)))))) ∨ p4)) ∨ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69046832221249321287475657998 : ((p5 → (((p1 ∧ True) ∧ ((((p2 → p3) → p3) → (p3 → (((True ∧ (p2 ∧ (False → (p1 → p1)))) ∧ p3) ∨ p1))) ∨ p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44441938501969548299969463387 : ((((p1 → ((p4 ∧ (p1 → p1)) → ((True ∧ True) → (p2 → p5)))) ∧ (((((False ∧ p4) → True) ∧ (False ∧ p5)) → False) → p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116261185456374352088304163720 : (((p1 ∧ (True → p5)) ∨ ((((p4 ∧ p5) ∨ (True ∨ p4)) ∨ (((p1 ∨ p3) → True) → ((p5 → p2) ∧ p3))) → (p1 ∧ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207279121603697746477918547487 : (((((p3 ∧ p3) → True) → p3) ∨ p1) → (p1 ∨ ((p5 → (((p5 ∨ (True ∧ p3)) ∨ p2) ∧ (p5 ∨ (((False ∧ p2) → False) ∨ p4)))) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∧ p3) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313226801630678238930938789583 : (p3 ∨ (((p3 ∧ p5) ∧ ((p5 ∧ ((p4 ∧ p3) ∧ ((p3 ∨ True) → True))) ∧ ((False ∨ (p4 ∨ (True ∧ p1))) ∨ ((True → p3) ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429645563448359624743306903792 : ((((((p3 ∧ p5) ∧ ((p1 ∨ ((False → p4) → ((p3 → p4) → p5))) ∧ True)) ∨ (p3 ∨ (((p1 ∧ p4) ∧ p1) ∧ True))) ∨ (p1 → p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84617394366034547412110190292 : (((p2 ∨ (((p3 ∨ p3) → (p1 ∧ True)) → (False → (p3 ∧ ((False ∨ p5) → p5))))) → (((p2 ∧ p3) → (False ∨ (False → p5))) ∧ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((p3 ∨ p3) → (p1 ∧ True)) → (False → (p3 ∧ ((False ∨ p5) → p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212489141121644024785006258632 : ((p4 ∨ ((p2 ∨ p4) ∨ True)) ∧ (True → (((((p4 ∨ p4) ∨ (p3 ∧ p4)) → (p4 ∧ (p1 ∧ p4))) ∧ p2) ∨ (p5 ∨ (True ∨ (p4 ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205683001601329176760976911009 : (((p4 ∨ p1) ∨ (p1 ∧ (p3 ∨ p4))) ∨ ((True ∨ p3) ∨ ((((True ∧ (True ∧ (p3 ∧ (p3 → p3)))) → ((p5 → p2) ∨ p4)) ∨ p3) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677356053447666655162088635430 : (((((p3 → (p2 ∨ (p2 ∧ ((True → (True ∧ (True ∧ ((p5 ∨ p3) ∧ (p1 ∧ p3))))) → p2)))) ∧ p5) ∨ ((True → (p1 → p4)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157535646290807543500525019953 : ((((((((True ∧ p5) → p5) → p1) ∨ (p4 ∨ ((True ∨ False) ∧ p4))) ∧ True) ∨ p3) → (p1 ∧ p5)) ∨ (False → ((p3 ∨ p3) ∧ (p2 ∧ p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135723363576810389818622457707 : (((((((True ∨ p2) ∧ False) ∨ (p1 ∧ ((p5 ∨ p3) ∨ True))) → p2) ∧ p4) ∨ (p1 ∨ (p5 → ((False ∧ p3) ∨ p3)))) ∨ (p5 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118476178759963121851816346370 : ((p3 ∨ (((p5 ∨ (((False ∧ (p2 ∨ True)) ∧ p4) → (((p5 ∨ p4) ∧ (p5 → (p2 ∧ False))) ∧ p4))) → p1) ∧ (p5 ∨ p5))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112385557286694316332867542305 : (((((p5 → (((p5 ∧ p3) → p2) → (p5 → ((False ∧ False) ∨ True)))) → ((p5 → (False ∨ p5)) ∨ (True ∧ p1))) ∧ p3) → p5) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135656246367322541357967465580 : (((((p3 ∨ p2) ∨ True) → ((p4 ∧ ((p3 ∧ (p2 → True)) → (p4 → False))) ∧ False)) → ((p1 ∨ (p3 ∨ p2)) ∨ p5)) ∨ ((p1 ∧ True) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790881339379256049467225663778 : (((p5 ∨ (p3 → (((((p3 → False) ∧ ((((p4 → (p3 → True)) ∧ p5) → p3) → p4)) ∨ (p5 ∨ p4)) → p4) → ((p4 → p4) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248365063230094650129196612038 : ((p2 ∨ p3) ∨ (p4 ∨ (((p2 ∧ p3) ∨ (p2 → True)) ∨ ((False → ((p3 ∨ (p4 ∧ (p2 ∧ ((p3 → p2) ∨ p2)))) ∧ (p3 → p3))) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43885906799049487787546314453 : ((((p5 ∧ (((p3 ∨ (p3 ∧ (p1 → ((((p1 ∨ p3) ∧ (p1 ∧ True)) → True) → True)))) ∨ p3) ∧ (False → True))) ∧ (p4 ∧ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2541442221917391350327787061 : ((((p5 ∧ True) ∨ ((p4 ∨ False) ∧ False)) ∧ True) ∨ (True → (p5 → (False ∨ (p3 ∨ ((True ∨ p1) ∨ (p1 → ((p1 ∨ p3) ∨ p1)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_317883134555227875225294960670 : (p4 ∨ ((True ∧ ((((p5 → p5) → (p2 ∨ p3)) ∧ (p3 ∨ (p3 → False))) ∨ ((p5 ∧ (((p4 → p1) → True) ∧ (p4 ∨ p5))) → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299456289192014127835197217380 : (False ∨ ((p4 ∨ (((((((p3 ∧ ((False ∧ p3) ∧ (p4 ∧ p3))) ∧ p5) ∨ False) ∨ (False ∧ (True ∧ p5))) ∨ True) ∧ (p4 ∨ True)) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65392758836233382532133330512 : ((p3 ∨ (((False ∨ p5) ∧ ((p4 ∧ False) → p5)) ∨ (((p5 → ((p4 → p3) ∨ p2)) ∧ (True ∧ (False ∨ (False ∧ True)))) ∨ (p3 → p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_61425119205264423998143742288 : ((p1 ∧ ((((p1 → p4) ∧ (p5 ∧ ((p4 ∧ p2) → (p5 ∧ ((True → (p1 ∧ p2)) ∧ p1))))) ∧ ((p2 ∧ p3) ∨ (p1 ∨ p4))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157784087386563770551450736566 : ((((True → ((((p3 ∨ p2) ∧ True) ∨ False) ∧ p2)) → (p4 ∨ p2)) ∨ ((False ∧ p1) ∨ (p2 ∨ p5))) ∨ (p4 → (((p1 ∨ p1) ∧ True) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53901065432119877240351900729 : (((p3 ∧ (((p1 ∨ (True ∨ p3)) → p4) → (p2 ∧ p5))) ∨ ((((p3 → (p3 → (p3 ∨ (p3 ∧ p5)))) ∧ p2) ∨ p4) ∨ (False → p1))) ∨ p1) := by
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
theorem thm_5_vars_138378730674112478455223417009 : ((p4 → (((p1 ∧ False) → True) → ((p3 ∧ (((True → p1) ∨ (p1 → (True → (p5 ∧ False)))) ∧ (False ∨ p4))) ∨ True))) ∨ ((p1 → p1) → False)) := by
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
theorem thm_5_vars_148101465617713302794001075975 : (((((p4 ∨ (p3 ∧ (((p1 ∧ (True → p1)) ∨ (p5 ∧ p2)) → False))) ∧ True) → (p1 → p2)) → (p1 ∨ p4)) ∨ ((p4 ∧ True) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54149344371487902736833923933 : (((p1 → ((True → (p1 → (True ∨ p5))) → (False ∧ p4))) → (((((True ∧ p5) → (p1 ∧ (p3 → p4))) → (False ∨ False)) ∧ p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64718266442436117056373262582 : ((p1 ∨ (p3 → (True ∧ ((p5 ∨ ((p2 ∨ ((p5 → p3) ∨ ((p2 ∧ ((p4 → p5) ∧ (p1 → p1))) → False))) ∨ (p1 ∨ p4))) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345646667452208409959701008900 : (p3 → ((p3 ∧ (p5 → (((p3 ∧ ((False ∧ (True ∧ p4)) → (True → False))) → (p5 ∨ ((p1 ∧ ((p1 → p2) → p5)) → False))) → p1))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42331495531801191783055311374 : (((p3 ∧ ((p3 ∨ (False ∧ (False ∧ ((p4 ∧ (p2 ∧ (p5 ∨ p5))) → ((p5 → ((p3 ∨ (p1 ∨ p5)) → True)) ∨ True))))) ∧ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680997187024366679904440695839 : (((((p3 → True) ∨ (True ∧ ((p5 ∧ ((p1 → (p1 ∨ p2)) ∧ p5)) ∨ (p5 ∨ ((True ∧ p4) → False))))) → (((p3 → p5) ∧ p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56129655030767850720073396905 : ((((p3 → p5) ∨ (p4 ∧ p2)) ∨ ((((p1 ∨ False) ∧ ((p1 ∨ p4) ∨ p3)) ∧ (True ∨ (p4 → ((True ∨ p4) → p2)))) ∨ (True ∨ p1))) ∨ p1) := by
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
theorem thm_5_vars_228040500228893578742294521579 : ((p3 ∧ (p5 → p5)) ∨ (((p3 ∧ ((p3 → p4) ∧ (p4 → p4))) ∧ p3) → (((p3 → p1) ∧ ((p3 → p2) ∨ ((p5 ∨ False) ∧ True))) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339506550355121349124520785151 : (p1 → (False ∨ (((True → ((p2 ∧ (p1 → p2)) ∧ p4)) ∧ p1) → ((True → (p4 ∨ (False ∧ p4))) ∧ ((((p4 ∨ p2) ∨ p5) ∨ True) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147044471013467438518750996892 : ((((False ∨ ((p1 ∨ (p5 ∧ (p1 ∨ ((p4 ∧ p5) → p1)))) ∨ p5)) ∨ (False → ((p1 → p4) ∨ p1))) ∧ False) ∨ ((p1 ∧ (p2 ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135860406874313029455515932476 : (((((p5 ∧ (p1 → ((False → p5) → (p4 ∧ p4)))) ∨ p4) → p1) ∨ (p2 ∨ ((p1 ∨ p3) ∨ (True ∨ (True ∨ True))))) ∨ ((p3 → True) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51589086345478006597475608895 : (((False → (p1 ∨ (((p4 ∧ p2) ∧ ((p3 → True) → ((False ∧ False) ∧ (p4 → p5)))) → p1))) → (p1 ∧ (((p4 ∨ p5) ∨ False) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



