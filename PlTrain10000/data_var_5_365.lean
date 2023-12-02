variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193923389968573983265305918069 : ((p1 ∨ (p1 ∧ (((False ∧ True) ∨ (p1 → p4)) ∧ p4))) → (((((p2 ∨ True) → False) → p5) → p2) ∨ ((True ∧ (p1 ∨ (p2 ∨ p3))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327822952199781763076572512460 : (True → ((((p4 ∨ p1) → ((p4 → ((((((p1 → p4) ∧ True) ∨ (True ∨ False)) ∨ p1) ∨ p2) → p2)) → p5)) ∧ (False ∨ p3)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352012138322037964558125262230 : (p4 → ((p5 ∧ (((p2 → (p1 ∨ True)) ∧ p1) ∧ False)) ∨ ((False ∨ ((p1 ∧ p2) ∨ True)) ∨ (((p4 ∨ False) ∨ (p3 ∧ p4)) ∨ (p5 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_111928280189912480252731988346 : (((((p5 ∧ (True ∨ (p5 ∧ (p2 ∨ p5)))) ∧ (p2 ∧ True)) ∧ ((((p2 ∧ p3) ∨ False) ∨ False) ∨ ((False ∨ p5) ∧ False))) ∨ False) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177969376107968712192783206727 : ((((False → p2) → ((((p3 ∨ p5) ∧ True) ∨ p5) ∨ (p5 ∨ False))) ∨ p4) ∨ (((p3 ∧ ((p5 ∨ (True → (True ∧ True))) → p1)) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634724209332166961221654075433 : (((((((True ∧ (p3 → ((p3 → ((p1 ∧ p3) ∨ (p2 → p1))) ∧ (False ∨ p4)))) ∧ (p2 → True)) → p1) ∨ (p5 ∨ (p5 ∨ p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177624671023114459906071321193 : (((((((p3 ∨ ((True ∨ p5) → p1)) → p3) ∧ p5) ∧ p4) ∧ p4) ∧ False) ∨ (((p3 ∨ False) → True) ∧ (((p2 ∨ True) ∨ True) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40462770338172877581506915428 : ((((((False ∧ p3) → p4) ∧ ((((((p2 ∨ (p3 → (True → p4))) ∧ ((True ∨ False) → False)) → False) ∨ p3) → p4) ∧ p3)) ∨ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299355304969517250067434182432 : (False ∨ (((True ∧ p2) ∧ ((((p1 → ((p5 → (p5 ∨ p5)) → ((p1 ∧ True) ∧ ((p5 → p4) → p4)))) ∧ (p5 ∨ True)) ∧ p1) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148522440479282133173661221540 : ((((((False ∧ (p2 ∧ p5)) ∨ (False → True)) → p2) ∨ (p5 → p4)) → (p1 ∧ ((False ∨ p5) ∨ (False ∧ False)))) ∨ (((p1 ∧ p1) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177258934211769073073033582770 : ((False ∨ (((p5 → False) ∨ (p2 ∧ True)) ∨ ((p3 ∧ (p5 ∨ p2)) → True))) ∧ (p4 ∨ ((True → ((p5 ∧ p4) → p3)) ∨ ((p3 → p5) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118157275043583137725996732880 : ((False ∨ ((((p4 → True) ∨ p1) ∨ p3) → (((True → (p4 ∧ p3)) ∨ (((False → ((False ∨ p2) ∧ p2)) → p4) → p4)) ∧ p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115050714670633552660533579726 : (((((p5 ∨ p4) → (((p5 → p1) → (True ∨ False)) → p5)) → p5) ∨ ((p1 ∨ True) → (True ∨ (p4 → (p4 → (p4 ∨ p1)))))) ∨ (p3 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_204621354998105584555970447585 : ((((p2 → p3) → (p3 ∨ p3)) ∨ False) ∨ ((True → (p4 ∨ (((False ∧ (p1 → (True ∧ ((True → p3) → p2)))) ∧ False) → (True ∧ p3)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264035504421611438533737245876 : (True ∧ ((((p3 → p3) → ((p1 → (p3 ∨ p1)) ∨ True)) → True) ∧ ((p5 ∧ (((False → False) ∨ False) → (False ∧ (p1 ∨ (p4 ∧ p4))))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254844419568602407018581355542 : ((p3 ∧ p5) → (((p2 ∧ (p1 ∨ p4)) ∧ p2) ∨ ((((p4 ∨ ((False ∨ (p1 → (p5 ∨ p5))) ∨ p5)) ∧ p4) ∧ (p4 → p4)) ∨ (False ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311825411074317821443111508415 : (p2 ∨ (p1 ∨ ((p3 ∨ (p3 ∧ ((p1 ∨ (p2 ∨ False)) → (p3 → ((False → True) ∧ p2))))) → (p4 → ((p5 ∨ ((p1 ∨ p4) ∧ p4)) ∧ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337520966476668972179843116468 : (p1 → ((((((True ∨ p5) → (True → (((p5 ∧ p3) ∨ (p4 ∧ p5)) → True))) → p2) ∨ (True ∨ p3)) ∨ p1) ∨ (p5 ∧ ((p2 ∨ p5) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161786515991268200973324777674 : ((p4 ∨ (p5 → (((((p4 ∨ p5) ∨ False) → p2) ∧ (False ∨ (False ∨ False))) ∨ ((p2 ∧ p3) ∧ False)))) → ((p2 → p3) ∨ (p4 ∨ (False → False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76708335488273947984033752255 : (((((p4 ∨ p2) ∨ (((False ∧ (p4 ∧ (p5 ∧ p4))) → False) ∧ ((False ∨ p1) ∨ p4))) → (((p5 ∨ (True ∨ p3)) ∧ True) ∨ p3)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ p2) ∨ (((False ∧ (p4 ∧ (p5 ∧ p4))) → False) ∧ ((False ∨ p1) ∨ p4))) → (((p5 ∨ (True ∨ p3)) ∧ True) ∨ p3)) := by
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
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161754008515562716716690773659 : ((p4 ∨ (((True ∧ ((p4 ∨ p1) ∧ ((p1 → (((p3 → True) ∧ True) → p2)) ∨ p4))) → False) ∨ True)) → (((p5 ∧ p5) ∨ (p2 → p2)) ∨ False)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_975187005397940633450164981024 : ((((p3 → p3) → ((p1 → (((p2 ∨ (True ∧ ((p1 ∨ (p5 → True)) → (((p3 ∨ p1) ∧ p4) ∧ (p1 → p5))))) → p1) → p4)) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215543647676226972979843898735 : ((p4 ∧ (p3 → (p4 ∨ p2))) ∨ (((p5 ∧ (p3 ∧ True)) ∨ True) ∧ ((((p4 ∨ (False → p1)) ∧ ((p5 ∧ False) ∨ True)) ∨ False) ∨ (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158283687237069775187093208969 : ((((p3 ∧ p4) ∧ p4) → ((((False ∧ p3) ∧ p5) ∨ (p2 ∧ False)) ∧ (((False ∧ p4) → p1) → p5))) ∨ (p3 → (p4 → ((p2 ∧ True) ∨ p4)))) := by
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
theorem thm_5_vars_621674205636540663192569415292 : ((((False ∧ (p3 ∨ (((True ∨ p2) ∧ (p2 → ((p3 ∨ (((True ∨ p2) → (p4 → (True ∧ (p4 ∨ True)))) ∧ p4)) ∨ True))) ∨ False))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330416552484881016688720478005 : (True → (p3 ∨ ((((p1 ∧ p2) → (True → (((p4 ∨ ((True ∧ p4) ∧ ((((False ∨ p1) ∧ p2) → False) ∨ True))) ∧ p3) ∨ p3))) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61543460861401772505695575468 : ((p1 ∧ ((((p5 ∨ ((p4 ∧ p1) ∧ (p5 → p5))) ∨ True) → p4) ∧ ((((p3 ∧ False) ∨ True) → (True ∧ (p4 → (p3 → p1)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68090522492265994222387596252 : ((p2 → (p5 ∨ ((False ∨ (p1 ∨ p5)) → (((p5 ∨ (True ∧ p2)) ∨ p1) ∧ (((True ∧ (p1 ∧ False)) ∧ p5) ∨ ((p4 ∧ p2) ∨ p2)))))) ∨ p2) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214235118857744557453916781439 : (((True ∧ (p4 → p2)) → p3) ∨ (((((p1 ∨ (p1 ∧ ((p1 ∨ p2) ∧ p3))) ∨ p4) ∧ (False ∨ p3)) ∧ (True → (False ∧ p4))) → (p2 → False))) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h12 := h4 h11
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h23 := h4 h22
          -- We need to get the left conjuct of h23 based on <expert-advice>.
          let h24 := h23.left
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h28 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h29 := h4 h28
          -- We need to get the left conjuct of h29 based on <expert-advice>.
          let h30 := h29.left
          -- False on the left can always be used.
          apply False.elim h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h35 := h4 h34
      -- We need to get the left conjuct of h35 based on <expert-advice>.
      let h36 := h35.left
      -- False on the left can always be used.
      apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49069791662685130320157912904 : ((((p2 ∨ ((((((p4 ∧ p2) → p4) ∧ (p4 → p3)) → p2) ∧ p4) ∨ ((p5 → p3) ∧ p3))) ∨ (False → p5)) ∨ ((p1 → p2) ∧ p3)) ∨ p4) := by
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
theorem thm_5_vars_134183728613362110445689759119 : (((((((p5 → False) ∨ (p5 ∧ p2)) ∨ ((p3 ∨ False) ∨ p2)) ∨ p3) ∨ ((p3 → (True → p4)) ∧ (p1 → p3))) ∨ False) ∨ (p1 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592024093007315425345306002207 : (((((p2 ∧ (((((True ∧ p1) ∨ p2) ∨ True) ∨ (p1 → p4)) → (((p3 → p1) → (p2 ∧ False)) → (False ∧ False)))) ∨ (True → True)) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148397459673414163615765057677 : (((p1 ∨ ((p3 ∨ (p1 ∨ (p1 ∨ ((p2 ∧ (False → p3)) → p4)))) ∨ p1)) ∨ ((p3 ∧ (p3 ∨ p3)) → p2)) ∨ (p2 → ((False ∨ False) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329688949640423581028556136048 : (True → ((p3 ∨ p2) → (p1 → ((p3 ∨ False) ∨ ((((p3 → p5) → (((p1 ∧ p2) ∧ (p3 ∧ p5)) ∧ p3)) ∧ ((p3 → False) ∨ p3)) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (p3 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h10
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50667571469351227372895434507 : ((((p5 → (((p4 ∧ p3) ∧ p2) → False)) ∧ (False ∨ (((p1 → (p2 ∧ False)) ∨ p4) ∧ (p5 → p3)))) → ((False ∨ p5) ∨ (True → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689048360621999468801656472688 : (((((((p2 ∨ True) → (p4 ∨ p2)) → (((True ∧ p5) → p4) ∨ (p5 ∧ True))) ∨ p5) ∨ (((p2 ∧ p5) ∨ p3) → (p1 → (False → p3)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196742945547050058495884900817 : (((((p3 ∧ p1) → p1) ∧ (p2 ∧ False)) ∧ p3) ∨ ((p1 → p4) ∨ (p1 ∨ ((True ∧ p2) → ((p4 → (p3 ∨ p2)) ∨ (p2 ∨ (p5 → True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146567785100765000106113045988 : ((p5 ∨ (p3 ∨ (((p2 ∨ ((p5 ∨ p5) ∧ p5)) ∨ p3) ∨ (((p1 ∨ (p1 → (p2 ∨ False))) → p4) ∨ True)))) ∧ (((True → p5) ∧ False) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42216137647381270662953721060 : (((False ∧ (((p4 ∨ (p3 ∧ p4)) ∨ (p1 → (p3 ∧ (p1 → ((True ∨ (p1 → (p4 ∨ ((p3 ∧ p4) ∧ p4)))) ∨ False))))) ∨ False)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216519237482208378827159974952 : ((p5 → (False ∨ (p3 ∧ p4))) ∨ (((True → p5) → (((True ∨ True) ∨ p5) → ((p5 ∨ (p4 ∧ (False ∧ (p3 → (p3 → False))))) ∨ p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258781747960798421212582076044 : ((True → False) → (((False ∧ (p1 ∨ ((p1 ∨ (True → p1)) ∧ (False ∨ (False ∨ p4))))) ∧ (p4 ∧ (p5 → False))) ∨ (p2 ∧ ((p5 → p2) ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61553642167612804621899234818 : ((p1 ∧ (((p1 ∧ p1) ∨ ((False → (p3 → p4)) ∧ p2)) ∧ ((p5 → (((p5 ∨ p3) ∨ (p3 → p5)) → (p3 → (p5 → p4)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191904839058823282907355914514 : ((p5 ∨ ((True → (p1 ∨ p1)) ∨ (p4 ∧ (p4 ∧ p3)))) ∨ (True ∨ ((p5 ∨ (((p1 ∨ (p1 ∨ p3)) ∨ True) → True)) ∧ ((p1 ∧ p5) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41924342237549770056621706644 : ((((p5 ∧ (p2 ∨ p4)) → ((p5 → (False ∧ (p3 ∨ (((((p2 → p1) ∨ ((p4 ∧ True) → True)) ∧ p5) ∧ p3) ∨ p3)))) ∨ True)) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
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
theorem thm_5_vars_191271807777071097466668887497 : (((p1 ∨ True) ∧ ((True ∨ p5) ∧ ((p3 ∧ p1) ∨ False))) ∨ ((p4 ∨ (((((p3 → p3) ∨ p3) → (True → True)) ∨ p1) ∧ (p4 → p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768284429420004093046177231553 : (((p5 ∧ ((((False ∧ ((p5 ∧ (p4 → p2)) ∨ ((p4 → (p3 ∨ p2)) → (p3 ∨ (p4 ∧ p1))))) ∨ p5) ∨ p3) ∨ ((p5 → p2) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86340216368748026566506296334 : (((((((p2 → (p4 → p2)) ∧ False) ∨ p1) ∨ True) ∨ p2) → ((False → (((p3 → p4) → (p2 → False)) ∨ False)) → (True ∧ (p3 ∧ p4)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 → (p4 → p2)) ∧ False) ∨ p1) ∨ True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (((p3 → p4) → (p2 → False)) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622091414171717144733593742318 : ((((p2 ∧ ((((True ∨ False) ∨ p3) ∧ ((p5 → False) → (p2 ∧ (((True ∧ True) ∨ (p2 ∧ False)) ∧ True)))) ∨ (p3 ∧ (p1 ∨ p5)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64249860281011071133338790639 : ((False ∨ (p3 ∨ ((((p1 → p4) ∨ (True → (((False → (p3 → p1)) ∧ (True ∨ (False ∨ p5))) ∧ (p4 ∧ (p4 → p3))))) → False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184129388708290423363668491873 : (((p1 ∧ ((p2 ∨ p3) ∨ ((p3 → p4) ∨ (p4 → p2)))) ∨ p3) ∨ ((p3 → (p4 ∨ (True ∨ (p2 ∧ p2)))) ∨ ((p2 ∧ p2) ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157673074266850261313041494628 : ((((False ∧ (p5 → p3)) ∧ (p4 ∨ (p3 ∧ (p3 ∨ ((p4 ∨ p3) ∧ p4))))) ∨ ((p3 ∨ p3) ∧ False)) ∨ (False → ((True ∧ True) → (p3 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206391511993048536126970191516 : ((p3 ∨ ((p3 ∧ (p4 ∧ p3)) ∨ p5)) ∨ ((p3 ∧ ((False ∧ False) ∨ (False → (p4 ∧ p1)))) → ((False → (False ∧ ((p3 ∧ p4) ∨ p1))) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117682467464931789700737013116 : ((p3 ∧ (((p4 → (True ∨ p4)) ∨ p5) ∧ (((p2 ∨ p4) ∨ (p3 → (p3 ∨ (p1 → (p3 → (False → (True ∧ p4))))))) → False))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891742850838332348928576333242 : ((((((True ∧ (p4 → (((p1 → ((p1 → (p2 ∨ (p4 ∧ p5))) → True)) → (p5 → p3)) ∨ p4))) → p4) ∧ p2) ∧ (p4 → (True ∨ False))) → p4) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ (p4 → (((p1 → ((p1 → (p2 ∨ (p4 ∧ p5))) → True)) → (p5 → p3)) ∨ p4))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310490386662931193279214275939 : (p2 ∨ (((p3 ∨ (p3 ∨ (p4 ∨ p3))) ∨ True) ∨ (((p5 ∧ False) ∧ False) ∨ (((p4 → (False → (False → (p5 ∧ (True → True))))) ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661007950701493692144874529468 : ((((((False ∧ (((((True → p3) → True) → (((False → p3) → p2) → p3)) ∧ False) ∧ (True ∨ p4))) → p5) ∧ (False → False)) → (p2 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234029968552224879921620117512 : ((p5 ∨ (False → True)) → ((p2 ∨ ((p4 ∧ p5) ∨ p5)) ∨ (((p3 → p4) ∨ False) → (p5 ∨ (True ∧ (True ∨ (p4 ∨ ((p1 ∨ False) → p1)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166272197532268076193085405444 : ((p3 ∧ (p4 ∨ (p2 ∧ (((((True ∨ True) ∧ ((True ∨ True) → p4)) → p2) ∨ True) ∨ p1)))) ∨ (((p3 ∨ (p1 ∨ True)) → (p4 → True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214707030706400427206074786317 : (((False ∧ p4) ∨ (p3 ∧ p5)) ∨ ((p4 → (((p4 → p3) ∨ p5) ∨ (p1 ∨ (True → (((False → p2) ∧ True) ∨ (p4 → (p1 ∧ p2))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679393979846781552722471885286 : ((((p4 → (True ∧ (p1 ∨ ((p4 → (p4 → ((p3 → (p2 ∨ (False ∨ False))) ∨ p2))) ∨ (True ∨ p1))))) ∨ (False → ((True → p4) → p2))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199333565338214684749418099053 : ((((((False ∨ p5) → p1) → p5) → p4) ∨ True) → ((False ∨ (((p2 ∧ p2) → p5) ∨ (False → ((p1 ∧ (False ∧ (False ∧ p2))) → p4)))) ∨ True)) := by
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
theorem thm_5_vars_738542896733870590289419069214 : ((((p1 ∧ p5) ∨ (((p3 ∧ ((p3 ∨ (((p1 → (True ∧ p3)) ∧ p1) ∨ True)) ∨ ((p3 ∧ (False ∨ p1)) ∨ (True ∧ p1)))) → p5) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174443883851553187465219836409 : (((((True → p1) → (p5 ∨ True)) ∨ (p1 ∧ p3)) → (((p1 ∧ p3) ∨ p3) ∧ p5)) → (p5 ∨ (((False ∨ True) ∧ p5) ∧ ((p5 ∨ p1) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → p1) → (p5 ∨ True)) ∨ (p1 ∧ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302572045487761302324174355770 : (False ∨ (p1 ∨ (((False ∨ ((True → False) ∧ (((((p3 ∧ ((False ∨ p1) ∨ p3)) ∧ p3) → p5) → False) ∨ p2))) ∨ True) ∧ (p5 ∨ (p2 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_705075981952261340706813500945 : ((((p4 → (((True ∨ False) ∨ p5) ∧ (p2 ∧ (p1 ∧ p2)))) → ((((p4 ∧ (p3 ∧ (p2 ∧ (p2 → p1)))) ∨ p4) ∨ (p1 → p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135189316659670298892635830654 : ((((((p1 → (p3 ∧ ((p4 ∧ (p5 ∧ p5)) ∧ False))) ∨ (True ∨ (p4 ∨ p5))) ∨ (p1 ∨ p5)) → p1) → (p5 ∧ p3)) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133662591459412153358273248925 : ((((p1 ∧ (p5 ∨ ((((True → p4) ∨ (p1 → p1)) → p5) → ((p1 → False) ∧ (p2 ∨ p1))))) ∨ (p4 → p1)) ∧ True) ∨ (p1 → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47174054204460644229873770461 : ((((p2 ∧ ((False ∨ (((True ∧ False) → p4) ∨ p4)) ∨ ((False → p4) ∧ False))) ∨ (p3 ∧ (p4 ∧ ((p2 → p3) ∧ p1)))) ∨ (p5 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90965687319448707278987388862 : (((False → p1) ∧ (((p1 → False) ∧ (p1 ∧ (((False → False) ∨ (True → (True ∨ p3))) ∧ p3))) ∧ (True ∧ ((False ∧ p3) → (p2 → p3))))) → p2) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h5.left
    let h14 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h21 := h6 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111998109588401868209053762174 : ((((((p5 ∨ p3) ∧ True) ∨ p3) ∨ (p2 ∨ ((p4 ∧ False) ∧ ((p5 ∧ (p1 → p5)) ∨ ((p1 → p4) ∧ (False ∨ p5)))))) ∨ True) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186317588926183429829951419206 : ((((((p5 → (False → p5)) ∨ False) ∧ False) → (False → False)) → p5) → ((((p5 ∨ (p1 ∨ (p5 ∧ True))) ∧ (p1 → True)) ∧ (p5 ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 → (False → p5)) ∨ False) ∧ False) → (False → False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671964676786126564700812483321 : (((((((False ∨ (p1 ∨ ((False → False) ∧ False))) → (((p4 ∧ (p3 → p3)) ∧ p2) → (p3 ∧ p2))) ∨ p2) ∨ p2) → (p2 ∧ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254181856165840215519315027635 : ((p2 ∧ p1) → ((p5 → p5) ∧ ((p4 → p2) → ((p5 ∧ ((p4 ∧ ((((p2 ∧ p3) ∧ p3) ∨ False) ∧ p5)) ∨ p5)) ∨ (p2 ∨ (p5 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233966479065417688130529332126 : ((p5 ∨ (p2 ∧ p4)) → (((p4 ∨ (p2 ∨ (False ∨ p1))) ∨ p4) ∨ (((p1 ∧ (False ∧ (p5 ∧ p2))) ∨ (False ∨ True)) → (True ∧ (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346281569819469924726010683120 : (p3 → ((((((False → True) ∨ True) → ((((p4 ∨ (False → True)) ∧ p3) ∧ (((p5 → p3) ∨ p3) → p3)) → p2)) ∨ True) ∧ True) ∨ (p2 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594926545053975381388505100940 : (((((p3 ∨ (p2 ∧ ((p3 ∧ (False ∨ False)) ∨ (((p1 → p1) → False) → p1)))) ∧ (((p3 ∧ p5) ∨ True) ∧ ((p3 ∨ p2) ∨ p1))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190346926155651420598620850315 : ((((p1 ∧ (p5 ∨ p4)) ∨ (p3 → (False ∧ p5))) ∨ False) ∨ (p4 → ((((p4 → False) ∧ p2) ∨ (p5 ∧ (p4 ∨ ((True ∨ True) ∧ p4)))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113483603658973926896579237308 : ((((p4 ∧ (((False → ((((p4 ∨ p1) ∨ True) → (p5 ∧ p3)) ∨ p4)) ∨ (True ∨ p2)) → p5)) ∨ (False → p3)) ∨ (True ∨ p2)) ∨ (False → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171324755568953982389672817409 : (((((p3 ∨ (False ∨ True)) ∧ ((p1 → True) ∧ (p4 ∧ (p4 ∧ p2)))) ∨ False) ∧ p2) ∨ (((False ∧ False) → ((p3 ∨ (True ∨ p5)) ∧ p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_384079897635536965078193915126 : ((((((p5 ∨ ((p2 ∨ (((p5 → ((p4 → (p1 → True)) ∧ False)) ∨ p3) ∧ p1)) ∨ ((p1 ∨ True) ∨ p5))) ∨ (True → p1)) → p2) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_150052797282612134068119877136 : ((True → (((p5 ∧ True) ∧ ((((p5 ∨ p3) → p1) → (p3 → p4)) ∨ ((p2 → (p1 ∨ True)) ∧ False))) ∨ p3)) ∨ ((p1 → p4) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41626686742365780096058066437 : ((((((p1 ∨ p4) ∧ (p2 ∨ p2)) → (p5 → True)) → (p5 ∨ ((((p3 → (True → False)) ∨ p2) ∧ ((False → False) ∧ p3)) → p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663387995836020615777184108996 : (((((p2 ∧ p3) → ((p3 → ((p5 → ((p4 → False) ∨ ((p3 ∧ p3) → True))) ∨ p4)) ∧ (((p3 ∧ p1) ∧ p5) → p5))) → (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345672268425666095825691222968 : (p3 → ((p1 ∨ ((p4 ∧ (p5 ∧ ((p3 ∨ True) ∨ p2))) ∧ ((p5 ∨ ((True ∨ (False ∧ p3)) ∨ (((p4 → p3) ∨ p2) → p2))) → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138157159952554589788405624727 : ((p1 → ((False → (p2 ∧ ((((p4 ∧ p1) → ((p5 ∧ (p3 → p1)) → p2)) ∧ (p1 → (True ∧ False))) ∧ p4))) → p4)) ∨ ((p5 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137702484351197384944671963654 : ((p1 ∨ (((((((False ∧ p5) ∨ p2) ∨ p1) → (p5 → p1)) ∨ (p5 → p1)) → (p4 → True)) → (p4 ∧ (p1 ∧ p4)))) ∨ (False → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112229782213331438844956831224 : (((p2 ∨ ((p5 ∨ ((True → False) ∨ ((p4 ∨ (((((p1 ∧ False) → False) → False) ∨ (False → p3)) → True)) ∧ p1))) ∨ p2)) ∨ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711352708505640831314670647788 : ((((p1 ∨ ((False ∨ p2) ∧ (p5 ∨ False))) ∧ (p5 ∧ ((False ∧ ((p5 ∧ True) ∨ p4)) ∨ (True ∨ (True ∧ (p3 → (p4 ∧ (p1 ∨ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214762000479122622896111460334 : (((p5 ∧ p4) ∨ (p2 ∧ True)) ∨ (((True ∨ (p3 → ((p4 ∨ (p5 → p2)) ∨ p1))) ∨ (p2 → (True ∨ False))) ∧ ((False ∨ (p5 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322206289853748179852921075134 : (p5 ∨ (((((p3 ∨ p3) → (p2 ∨ ((True ∧ (p3 → (((((p4 → p5) ∨ p5) ∨ True) ∨ (p4 ∧ p4)) ∧ p3))) ∧ p5))) → False) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179333849059743260249504970487 : ((p1 ∨ ((((p3 → p3) → (p5 → p4)) ∧ p5) ∨ ((True ∧ p1) ∧ p3))) ∨ (True ∨ ((p2 ∨ (False ∧ False)) → (p3 ∧ (True → (p3 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64097041098148046759439544616 : ((False ∨ (((p5 → (p4 ∨ ((False ∧ p3) ∧ (False → p1)))) ∨ p5) ∨ (((False ∨ p4) ∧ p5) → (p3 ∨ (((p1 ∧ p4) → False) ∨ p4))))) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40133112115466671619554323444 : (((((((p2 ∨ ((((p4 ∧ p4) ∨ ((p3 ∧ True) → p4)) ∨ p1) ∧ p4)) ∧ True) ∧ p1) ∧ (p2 ∨ ((p3 → p2) → p5))) ∧ p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314263852503811958839366490631 : (p3 ∨ (((p2 ∨ p3) ∧ ((((p1 ∨ p5) ∧ (p2 ∧ (((p1 ∧ (p3 → False)) ∧ p3) ∨ False))) ∨ (True ∧ p1)) ∧ True)) ∨ ((True → p2) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248745361681404344580025260746 : ((p3 ∨ p3) ∨ ((((p5 → p1) ∧ p4) → (False ∨ ((p5 ∨ p4) ∧ (p2 ∨ ((p4 ∧ p4) → (True ∨ (p5 ∧ ((False → p2) ∧ p4)))))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336227660938446037687762243396 : (p1 → (((p3 ∧ ((((p5 ∨ ((p4 ∧ p1) ∨ (p3 ∨ (p5 → True)))) ∧ (p4 ∨ (False ∧ p1))) ∨ True) ∧ p4)) ∨ ((True ∨ p2) → p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216012247094694399826045972452 : ((p5 ∨ ((p2 ∧ p3) ∧ p3)) ∨ (((True ∨ ((p4 ∨ (p1 → p3)) ∨ (p3 ∨ (p4 ∧ (p2 ∧ p3))))) ∧ (p3 → ((p1 ∨ p4) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708245255911732015872541941634 : ((((p4 → (((p1 ∨ p5) ∨ (p1 ∧ True)) ∨ p5)) ∨ ((p3 ∨ ((p3 ∨ p4) ∨ ((p3 → p3) ∨ p2))) ∨ (p4 ∧ (p4 → (True ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618136284356594383836235597573 : (((((False ∨ (False ∨ (p2 ∧ p2))) ∧ (p5 ∨ (((((True ∨ True) ∨ False) ∨ ((True → (False ∨ False)) ∧ p5)) ∨ False) ∨ (False → True)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118910332188118236077009846847 : ((True → (p3 → (((p2 ∨ (False ∧ ((True ∧ ((((p3 ∨ p4) → False) ∨ p4) ∧ p3)) ∧ False))) ∧ (p5 ∨ False)) ∧ (p5 → p5)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



