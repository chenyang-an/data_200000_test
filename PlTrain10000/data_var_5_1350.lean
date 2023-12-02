variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40781841804561377579447441489 : ((((p1 ∧ (True → (False ∨ (((p2 ∨ p2) ∨ (False ∧ (p4 ∧ (p2 → (p5 ∧ False))))) ∧ (((p5 ∨ True) ∧ True) → p2))))) → False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47038498688489953583609561929 : (((((False ∧ (((p1 ∧ p1) ∨ (p2 → (p1 ∨ p3))) ∨ (p5 → (True → (p1 ∧ p5))))) ∨ (False → p4)) ∧ (p1 ∧ p2)) ∨ (p4 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256059845225650984287739512038 : ((True ∨ p4) → (((p1 → (False → p3)) → p4) → (((((((p3 → True) ∧ (p2 → False)) ∨ False) ∨ p2) ∨ (p3 ∨ p4)) ∨ p2) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_68118039927019587255832776555 : ((p2 → (p3 → ((((p5 ∨ (False → (p2 ∧ p5))) → p4) → False) → ((((p3 ∧ ((p3 ∨ p1) → p4)) ∧ p4) → (p5 → p1)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135246856610406092768138514571 : ((((False ∧ p5) ∨ (True → (True ∨ (False → (((False ∨ (p3 ∨ (p1 ∨ p5))) ∨ (True → p3)) ∨ p5))))) → (p5 ∧ p5)) ∨ (True ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43819858154657159698775371895 : ((((p4 → (p2 ∨ (p1 → ((((p1 → False) ∨ p4) ∧ False) ∨ ((p1 → False) ∧ (p4 → (((p1 → p1) ∨ p4) → False))))))) → p4) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66855738679624122461234578668 : ((True → (p5 → (p1 ∨ (((p1 → (p3 ∧ ((p3 ∨ p4) → (((p3 → p4) ∨ p2) ∧ p2)))) → p3) → ((p3 ∧ False) ∨ (p5 ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116312850270636164276064554739 : (((p4 → (p5 ∧ False)) ∨ ((p1 ∧ p5) → (p2 ∨ (p5 ∧ (p5 → ((p1 ∨ p1) → (((p2 ∧ p2) ∧ True) ∨ (p1 ∨ p2)))))))) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309366422916535554704993004986 : (p2 ∨ ((((p4 → p3) ∨ p5) ∧ (p5 ∧ ((False ∧ True) ∧ (True ∨ (((p5 ∧ p1) → p4) ∨ (((p2 ∧ p3) → p2) ∨ True)))))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55120098588736098011698083991 : (((((p4 ∧ p2) ∧ (p5 ∧ p1)) ∧ p4) ∨ (((True ∨ False) ∧ (p2 ∧ (p3 → p3))) ∨ (p4 ∧ (p2 ∨ (((p1 ∨ p5) ∨ p2) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25374305177645407779716587191 : ((((p3 ∨ p5) → p5) → (((((False ∨ (p1 → p2)) → p4) ∨ p3) → ((p1 ∧ p3) ∧ (True → (True ∧ p5)))) ∨ ((p1 ∧ p2) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611082613661748387589438007601 : ((((((((False → p5) ∧ p5) ∨ True) ∨ ((False ∧ (p3 ∨ (((p4 ∧ p1) → p3) ∧ ((p3 → p2) ∨ (p3 ∨ p2))))) ∧ False)) → p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_55536449709773424915252218463 : ((((p5 → False) → ((True ∧ False) → p2)) → ((p4 ∨ (((p1 ∧ p5) → (p2 ∨ p5)) ∧ ((p2 ∨ (p2 → (p1 ∧ p3))) → p5))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261330031566939093929682524681 : ((p5 → False) → (((p5 ∧ ((((p1 → (p3 → (p5 → p5))) ∨ (False ∧ p1)) → (True ∨ False)) → p5)) ∨ (p5 ∨ True)) ∨ ((p1 ∨ True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336448127861788255049249062158 : (p1 → ((p5 ∨ (((p5 ∨ ((False → (False ∧ (p2 → (p2 → p2)))) → (p3 ∧ p5))) ∧ p3) ∨ ((p2 ∧ (p1 → p4)) ∧ (False ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199882185001041693107259676470 : (((((True ∧ p1) → False) ∧ p1) ∨ (p2 ∧ p2)) → ((True ∧ ((True → True) → True)) → ((((False ∨ True) → p4) ∧ p2) → (p4 ∧ (p1 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h3.left
  let h19 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h2.left
  let h21 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h28 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h29 := h18 h28
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780660536457090754231368604093 : (((p2 ∨ ((((True ∧ p1) → (p5 ∨ (p1 ∧ p1))) → p3) ∨ (p2 → (((p4 → p2) → p5) ∨ (p1 → (((p4 ∨ False) → p2) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111674487328738271655587818362 : ((((p3 → (False ∨ ((p1 ∨ (((p3 → (((False ∧ ((p4 ∨ False) ∧ p3)) → True) → p1)) ∧ p3) → p3)) → p5))) ∨ p5) ∨ True) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146467274161804173760834425327 : ((p3 ∨ (True ∧ ((((p1 ∨ False) → (p4 ∨ ((p5 ∨ (p5 ∧ True)) ∨ p3))) ∧ p2) ∨ (False → (True ∨ False))))) ∧ (((p2 ∨ p2) → p2) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177734050606554011650590221910 : (((((p2 ∨ p1) ∨ p1) ∧ (((True ∨ False) ∨ p3) → (p4 ∨ p5))) ∧ p3) ∨ (p4 → (p3 ∨ (p1 ∨ ((((False ∧ True) ∧ False) → False) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682848720961937103087045650041 : ((((((p3 ∧ False) → p2) → ((((((p3 ∨ p3) → p5) ∧ (p5 ∨ False)) ∨ True) ∨ False) ∨ p2)) ∧ ((((p2 → True) ∨ False) → p5) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215291995518721589912233706700 : ((p1 ∧ ((p2 → p1) ∧ True)) ∨ ((p2 ∧ ((p1 → p5) → ((p2 → (p1 → (p3 → (p2 ∧ p4)))) → (((False ∨ p3) → p2) → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110950934775492405409777532211 : (((((p4 ∨ ((False ∧ p3) ∨ (((((p1 ∧ True) ∨ False) ∨ p1) ∧ p5) ∨ (False ∨ (p3 ∧ True))))) ∧ p2) ∨ (p3 ∧ True)) ∧ False) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199477305336590847072854793243 : (((p2 ∨ (True ∨ (p3 ∨ (False ∧ False)))) ∨ p1) → (p4 ∨ (True → ((p5 ∨ (p2 ∨ ((p5 → (p2 ∨ True)) ∨ (True → p3)))) ∨ (True → True))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- False on the left can always be used.
          apply False.elim h14
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2661577714166460788822775753 : (((p5 ∨ p5) ∧ ((p1 ∨ p5) ∨ p5)) ∨ ((p3 → True) ∨ ((p1 ∧ (False → (p5 ∧ p2))) ∨ (((False ∨ (True ∨ p2)) → p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619581752144684134016683922597 : (((((False ∧ p3) ∧ ((p2 → ((p1 ∧ p2) ∨ p3)) → ((p1 ∨ (((p4 → p3) → True) ∨ (p2 ∨ (False ∨ False)))) ∧ (p2 ∨ p4)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258189650246471522010135078664 : ((p4 ∨ p4) → ((p1 → True) ∧ (((p5 ∨ p4) → False) → ((p5 → p4) ∧ ((False ∧ (p1 ∧ (((p1 ∧ (p3 → p1)) ∨ p2) → p1))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p5 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (p5 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116609071885492881026567820332 : (((True → p2) ∧ ((p1 → p2) ∨ ((((p5 ∨ False) ∨ ((True ∨ True) ∧ (p5 ∧ ((p2 → p4) ∨ p4)))) ∧ (False ∨ False)) ∧ True))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56853001245073887159797634416 : (((True ∧ (p4 → True)) ∧ (p5 → ((True ∧ (p1 ∧ (((False ∨ True) ∨ p5) ∨ ((p1 ∨ (p3 ∨ p5)) → ((p2 ∨ p3) ∧ False))))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41287247987863446810775574825 : (((((p1 ∨ ((False → p2) → (p1 ∨ ((p4 → True) ∧ p1)))) → (((p3 → True) ∨ True) → p5)) → (((p5 ∨ True) ∨ p5) ∨ p1)) ∨ p5) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41443133527946638040572446924 : ((((p2 ∨ ((False ∧ (p1 ∧ (True ∧ ((p2 ∧ p3) ∨ (True → p5))))) → p3)) → ((((p1 ∨ p5) ∨ p4) → False) ∧ (p2 ∧ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185351681122945840700344395365 : ((p4 ∧ (((p2 → p3) → p1) ∨ ((p1 → (p4 → False)) ∧ p1))) ∨ ((((False → p5) ∨ p3) → (p1 → ((p3 ∧ p5) ∨ True))) ∨ (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190581787482161428218096678295 : ((((p4 ∧ (p3 ∧ p1)) → (p3 ∧ (p5 → True))) → p5) ∨ (((((True ∨ p5) ∨ p4) ∧ (((p5 ∨ p3) ∧ (p5 ∧ p3)) ∧ True)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47339392528856125724988480905 : ((((p1 ∨ p2) ∧ ((p5 ∨ ((p3 ∧ (False ∧ False)) → False)) ∧ (((True ∧ p5) ∧ (p3 → (p4 ∧ (True ∧ p2)))) ∧ True))) ∨ (True ∨ p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710802312257348712880553708788 : (((((False ∧ False) ∧ ((p3 ∧ p2) ∨ True)) ∧ (p4 ∨ (((True → (p3 → ((True ∧ p4) → p4))) → ((p5 → (p5 ∨ p1)) ∧ False)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52026621816106948336170934851 : (((p1 ∨ (p1 ∨ (p2 ∨ (p1 → ((False ∨ (p3 ∨ (p2 ∨ (False → p5)))) ∧ True))))) ∨ (((((p1 ∨ p1) ∨ False) ∧ p1) ∧ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714327659824855849382181143012 : ((((((p3 → p1) → True) ∨ (False ∧ p3)) → ((((True ∨ (((False ∨ (p5 ∨ p3)) ∧ (p4 ∨ p3)) ∨ p2)) ∨ p5) → (p4 ∧ p5)) → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((True ∨ (((False ∨ (p5 ∨ p3)) ∧ (p4 ∨ p3)) ∨ p2)) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54548851249902098482279672688 : (((False ∧ (p5 ∧ (p4 ∧ (p5 ∧ (p5 ∧ p4))))) ∨ (p2 → (((p1 → (((p3 ∨ (p2 ∨ p1)) ∧ (p3 ∧ p5)) → p5)) → p5) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261335626852075418513176974198 : ((p5 → False) → ((((False ∧ ((True ∧ p5) ∨ p3)) ∨ p5) ∧ (((p2 ∨ False) ∨ p3) → p2)) ∨ (p5 → (p2 → ((p1 ∧ (p5 ∧ p4)) ∨ p5))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389317559776832431207687221193 : ((((((p1 ∧ ((p1 ∨ (p3 → p1)) ∧ (False ∨ p1))) → (p2 ∨ (p5 ∧ p3))) ∨ (((p3 ∧ False) ∧ p2) → ((p4 ∨ False) → p2))) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147035175660475046155819926415 : (((((p3 → (p1 → True)) → ((False ∨ (p4 → (p1 → (p1 ∨ True)))) ∨ p1)) → (False ∨ (p1 ∧ p3))) ∧ p2) ∨ (p4 ∨ (False → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812916403929852904704561868028 : ((((((p1 ∨ ((p1 → p3) → p2)) ∧ (True ∧ ((p3 ∧ (p4 ∨ p2)) ∧ (((True ∨ (True ∧ (p4 ∨ p4))) → False) ∨ True)))) ∧ p2) ∧ p2) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h7.left
    let h23 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h32 =>
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328568882359852840921444283997 : (True → ((True → ((((False ∨ True) ∨ (p2 ∨ p5)) ∨ ((p1 ∧ p5) ∨ p5)) ∧ (p4 ∨ p4))) → (((((p4 ∧ p5) ∧ p4) ∧ p2) → p4) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217456428780114051627312676977 : (((p5 → (p3 ∧ p1)) ∨ p4) → ((p3 ∧ ((True ∨ (p5 → (p5 → True))) ∨ p3)) ∨ ((((p2 ∨ p1) ∧ (p3 ∨ False)) ∧ p4) ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648910800614576291940675975189 : (((((((p1 ∨ (((p2 → (p5 ∧ (((p1 → p2) ∧ False) ∨ ((p5 → True) ∧ False)))) ∧ p3) → True)) ∧ p3) ∨ p4) → False) ∧ (p1 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26971327434816048083284240910 : (((p4 ∨ p4) ∨ (p3 → (((((False ∨ True) ∧ ((p1 ∧ False) ∧ p2)) → True) ∧ ((p5 ∨ (p4 ∧ ((p1 ∨ True) → p5))) ∨ False)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_339602242293163464507241123747 : (p1 → (p2 ∨ (((((((((True ∨ False) ∨ p1) ∨ (((p1 → p5) ∨ False) ∧ True)) ∧ p4) → (p1 → p5)) ∨ p1) ∨ (False → p3)) → p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153284406554586139344615363253 : ((p1 ∨ (((p4 ∧ (p4 → ((((p1 ∧ p5) ∧ p4) ∧ p3) ∧ (True ∨ (False → (p4 ∧ p2)))))) ∨ True) ∧ p3)) → ((p1 ∧ p1) ∨ (p4 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157300373704402060333448323514 : ((((p5 → False) → ((p4 ∨ p5) → ((p1 ∨ p4) → ((p4 ∧ (p1 ∨ (p4 ∨ p2))) ∧ p1)))) → p3) ∨ (((p3 → p2) → p5) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67838304664060303049579606466 : ((p2 → (((((((((p4 → (p5 ∨ p3)) → p3) → p1) ∨ ((p4 → p2) → p5)) → True) ∨ p3) ∧ (p5 ∨ True)) → p5) ∨ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177768623238470933528540274252 : (((True ∧ (p3 ∧ (p5 ∨ ((True ∧ ((p5 ∨ p3) ∧ False)) ∧ p1)))) ∧ True) ∨ (False → (((p3 ∨ p5) ∨ (p3 → ((p3 → p3) → True))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38306157458253294824025492772 : (((((((p3 → True) → (((False ∧ True) ∨ (p1 → (p5 ∨ p3))) ∧ p2)) ∧ p2) ∧ (False ∨ True)) → (p1 ∧ ((p4 ∧ p5) → False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58954738291480098302635226260 : (((p2 ∧ False) ∨ (p1 ∧ ((True ∧ ((True ∨ ((p2 ∧ p3) ∨ True)) → True)) → (p3 ∨ ((p3 ∧ True) ∨ ((p5 ∧ (p4 → True)) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134882686549399148451901616383 : (((p3 → (((p4 ∧ p2) → (p3 → ((p2 ∧ p4) ∧ ((True ∧ p2) ∧ True)))) ∨ (p3 ∧ ((p4 ∨ p5) → p2)))) → False) ∨ (p2 → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185489744876611864933051188603 : ((p2 ∨ (((True ∨ (p2 ∧ (p2 → (False ∨ p1)))) → p1) ∨ p4)) ∨ ((p3 ∨ (p2 → p1)) ∨ (((False → p4) ∧ p1) → (p2 ∨ (p1 ∨ p4))))) := by
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
theorem thm_5_vars_173235960591695261424981476231 : ((True → (((p3 ∨ True) ∨ (p5 ∧ ((p3 ∨ p5) → (p3 → True)))) → (False ∧ p4))) ∨ ((((p5 → False) ∨ ((True ∨ True) → p3)) → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116123501545660158101717520526 : (((True ∧ (p2 ∨ p3)) ∧ (((True → (p3 ∨ ((p1 ∨ p2) ∨ (p3 ∨ False)))) → (p2 ∧ ((p4 → p2) ∧ True))) ∨ (p4 ∧ p5))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167231838052489280145504171728 : (((False → ((p1 ∧ (True ∨ (((False → (p3 → p5)) → p2) → p4))) → (p4 ∧ p3))) ∨ p4) → (p5 → (((p5 ∨ p3) ∨ False) → (p2 ∨ p5)))) := by
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
      cases h1
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
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147273326859909483465546387440 : (((((((p3 ∧ p4) ∨ (p2 ∧ p2)) → ((p5 ∧ p4) ∨ p1)) → ((False → p2) ∧ (p1 ∧ False))) ∨ True) ∨ p5) ∨ (p2 → ((p2 ∨ True) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610254224722175941630234802962 : (((((((True ∨ ((False → True) → p3)) ∧ ((True ∨ False) → (False ∧ (((((p4 → p1) ∧ False) ∨ p1) → False) → p3)))) ∨ p3) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41750106719135628302660528206 : (((((p2 → (p1 → p1)) ∧ p3) ∨ (((False ∨ (((p5 ∨ True) ∧ True) ∨ (True ∧ ((p1 ∧ (True ∨ p4)) → True)))) → p1) ∨ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112709135846907735868998316331 : ((((p3 ∨ (((False ∨ False) → p2) ∨ ((p4 ∧ p5) ∧ ((p1 ∨ (False ∧ p3)) → p3)))) → (p4 ∧ ((p1 ∨ p3) → p4))) → p3) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47183601830600660090711838100 : ((((((p4 ∧ (p5 ∧ ((p2 ∨ p5) ∨ p3))) ∨ (p4 ∨ p4)) ∧ p4) ∧ ((p2 → (p2 ∧ (p3 → (p2 ∨ True)))) ∨ p2)) ∨ (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190314738382223625021853508794 : ((((p3 ∧ ((False ∨ p4) ∨ p4)) ∧ (False ∧ p3)) ∨ p2) ∨ (((False → (p5 → ((p2 ∨ ((True ∨ False) ∧ p5)) ∨ (False → p4)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708054372878055480674416993204 : ((((p3 ∨ ((p1 ∨ p4) → ((p4 ∨ False) ∧ False))) ∨ (((((p1 ∧ p4) ∨ (False ∧ False)) ∨ False) → (p1 ∧ (p2 → p4))) ∨ (False ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443026236410816233886454856392 : ((((((False ∧ ((((p1 ∨ False) → p2) → p4) → ((p4 → (p5 → False)) ∨ False))) ∧ p3) ∧ ((p4 ∧ p4) → p5)) ∨ ((True ∨ p5) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55191214463254112652857450027 : ((((p4 ∧ ((True → p1) ∨ p5)) → False) ∨ ((((p5 → (((p4 ∨ False) ∧ p4) ∨ False)) ∨ ((False → p2) → p4)) ∨ True) ∨ (p3 → p5))) ∨ p3) := by
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
theorem thm_5_vars_41812030823182603017715458274 : (((((p2 ∨ True) ∧ True) ∧ (((((p4 ∧ p4) ∨ p5) ∧ (p1 ∧ p4)) → False) ∧ ((True ∨ (p3 ∨ ((p3 ∧ p1) ∨ p2))) → p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611879644607141538991961873107 : (((((p5 → (((True ∧ p3) ∧ (((((p3 → (p3 ∨ True)) ∨ p3) ∧ (p5 ∨ p1)) ∨ ((False ∨ False) → p2)) ∧ p4)) ∨ p1)) → p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325024144174977645324730340040 : (p5 ∨ ((p3 ∧ True) → (p2 → (p1 → (((False → (p4 → ((p4 → True) ∨ p2))) ∨ p4) → (((p5 ∨ (p4 → False)) ∧ p5) ∨ (True → True))))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729932332839292558710886756857 : (((((p3 ∧ p5) → p4) → ((p2 ∨ (p3 ∧ ((True → ((p5 → p1) ∨ (p2 → ((p2 ∨ p3) ∨ (False ∧ p4))))) ∨ (p2 → p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112082659051574857916184796746 : ((((False ∨ p1) ∨ (((True → (p4 → p1)) ∧ (((p2 ∨ p2) ∧ (False → p2)) ∨ p4)) → ((p4 → (p2 ∧ False)) ∨ p1))) ∨ True) ∨ (p1 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149329711365577191933614214481 : (((True ∨ True) → (p5 ∨ (((((False ∨ p1) ∧ p2) ∨ (p5 ∧ True)) ∧ ((True → p3) ∧ p4)) ∧ (p5 ∨ p5)))) ∨ ((p4 → True) ∨ (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319275044810278482137508473855 : (p4 ∨ (((p1 → (p1 ∧ ((p5 → ((p5 → p3) ∧ p2)) ∧ p5))) → (p2 ∧ (p2 ∧ True))) ∨ ((p5 → p4) ∨ (False → (p1 ∧ (p3 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111914405222467870754041595747 : (((((((p1 ∧ p3) → p5) ∧ (p5 → ((False → True) → True))) → False) ∨ ((True ∧ (p1 ∧ False)) → (p1 ∨ (p4 ∧ p2)))) ∨ p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327681577095060558377028823135 : (True → ((((True → (((((((p3 ∧ (p1 ∨ ((p4 ∨ p4) → p5))) ∧ p4) → p3) → p5) ∧ p3) → True) → p2)) ∧ p3) ∨ True) ∧ (p4 → p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153518146386127281682986504298 : ((True → (((((p1 ∨ ((p5 → (p5 → ((p4 → (False ∧ False)) ∧ p4))) → p4)) ∧ p1) ∨ False) → True) ∧ p5)) → (p5 ∨ ((p5 ∧ True) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168632454764803508039038072343 : ((p4 ∧ ((((p3 → p1) → p5) ∧ (((p2 → (p3 → p4)) ∧ (True ∧ p1)) → False)) ∧ p3)) → ((((p5 → (False ∧ True)) ∧ True) ∨ True) ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588011847083619334608775344312 : ((((((p3 ∨ (False ∧ (((p2 ∨ p5) ∧ False) ∧ (p4 → ((p4 ∧ False) ∧ (p3 → p4)))))) ∧ (((True ∧ p5) ∨ p4) ∨ p4)) ∨ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56995911949751312012397617632 : (((p5 ∨ (p3 → p2)) ∧ (((p5 ∨ ((False ∨ (p1 → ((p5 ∧ (p5 → p2)) ∧ (p1 ∧ True)))) ∧ (p1 → (p3 → p3)))) ∧ p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622521887096131822769198638829 : ((((p3 ∧ (p1 → (p5 ∨ ((p1 ∨ (((p1 → (p4 ∧ (p4 ∧ p3))) ∨ p5) ∨ (((p3 ∧ (p2 ∧ p3)) → p4) ∧ p2))) ∧ p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185863104291776438404824307305 : (((((((p1 ∧ p4) → (p3 ∧ p2)) ∨ False) ∨ False) → p3) ∧ p4) → ((((p1 ∨ (p2 → True)) ∧ (p3 → (p3 → (p1 ∨ True)))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156801355440668540153019276284 : (((p5 ∧ ((p1 ∧ p3) ∨ ((True → p5) → ((True ∨ (False ∨ ((p3 → False) ∨ p5))) → p3)))) ∧ False) ∨ (True → ((p4 ∧ p2) → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180185500488524260952240378210 : ((((p2 ∨ (p3 ∨ (True ∨ False))) ∨ ((True ∧ p3) ∧ (p4 ∧ p5))) → p3) → (((p5 → ((True → (True ∧ True)) ∨ (False ∧ p1))) ∧ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p3 ∨ (True ∨ False))) ∨ ((True ∧ p3) ∧ (p4 ∧ p5))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185491473872718499376966489308 : ((p2 ∨ ((p3 ∨ (True ∧ (((p2 ∨ p5) ∨ p2) ∧ p1))) ∨ True)) ∨ (p4 ∧ ((p5 → p3) ∧ (((p5 ∧ (p3 → p1)) ∧ (p1 ∨ True)) ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258903934649021971486856080087 : ((True → p2) → (((False ∧ ((False ∨ (True ∨ False)) ∧ False)) → (((p4 ∧ (p4 ∧ (p5 ∨ p1))) ∧ p2) ∧ p1)) → ((p3 → (p4 ∨ p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65220045227948154241017635391 : ((p3 ∨ (((p4 ∨ (p4 ∧ False)) ∨ ((p3 ∨ (p2 → (p2 ∨ p3))) ∨ ((p4 ∨ ((p1 ∨ ((p2 ∧ p1) → p5)) ∧ True)) → p2))) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67698372843572929080380534775 : ((p1 → (p4 → (((p5 ∧ ((p5 ∨ p5) ∨ ((p2 ∨ True) ∧ p4))) ∨ p2) ∨ (((p5 → p3) ∧ (p4 ∨ p3)) ∨ (False → (True ∨ p1)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46893420502910370792823476278 : ((((((True ∨ (p3 → ((p1 ∨ (((p4 → ((p4 ∨ p1) ∨ False)) → p2) ∨ p1)) ∨ (p3 → False)))) → p5) → p4) ∨ p5) ∨ (False → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54497980174445730616263020296 : ((((p2 ∧ (p2 ∧ p5)) ∧ ((p2 ∧ True) ∧ p2)) ∨ (((p1 ∧ p3) ∨ (((True → p1) ∧ False) ∧ (p2 → p3))) → ((p1 ∧ p4) → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131618870368692321855276601652 : (((False ∧ (p3 ∧ p3)) ∨ ((p4 ∨ p2) ∨ (True ∨ (p4 ∧ ((p2 ∧ (True → p2)) ∧ ((p5 → p3) ∧ (True ∧ p1))))))) ∧ ((False → False) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53380453649899126996101413529 : (((((((p1 → p1) → True) ∧ p5) ∨ (p1 → (p4 ∧ True))) → p1) → ((p3 → (p4 ∨ p3)) ∧ (p3 ∨ ((True → p5) ∨ (p4 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111592654337030331578285994703 : ((((True → (((p1 ∨ (p5 → (p2 ∧ (p1 ∨ ((p2 → p5) ∧ (p4 ∧ (p5 ∨ False))))))) ∧ p4) ∨ (p3 ∧ p3))) ∧ p5) ∨ p5) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134357379201610754550481183443 : (((False ∨ ((((p5 → (((p4 ∨ p1) → (p4 ∧ True)) → True)) ∧ p1) ∨ p3) ∧ ((p2 ∧ p2) → (p1 → p4)))) ∨ p2) ∨ ((False → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156923715018556944450998953716 : ((((p5 ∧ ((p2 ∨ (p2 ∨ ((p2 → p3) → p3))) → (((p3 ∧ False) ∨ p2) ∨ True))) → p1) ∨ False) ∨ (p5 ∨ ((False → p1) ∨ (True → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204112919093845677314787176895 : (((((p3 ∨ p4) ∨ p4) ∧ False) ∧ p5) ∨ (p2 → (((((True → (p3 ∧ (p5 ∨ False))) ∧ p5) ∧ ((False ∧ p5) → (p5 ∧ False))) ∨ p2) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149835176396242166014543850108 : ((p1 ∨ (((((p4 ∨ p1) ∧ p1) ∨ (p4 → p3)) → False) ∨ (((True ∧ (True ∧ p1)) ∧ (p5 ∨ p5)) → p5))) ∨ (True ∧ ((p3 → p5) → False))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355868980757976483095321612645 : (p5 → (((p4 ∧ (p4 → False)) ∨ (((p3 ∨ p1) ∧ p3) → ((p5 ∧ (False → p3)) → (False ∧ ((p4 ∨ p5) → True))))) ∨ ((p3 ∧ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88093752822301394718706721396 : (((((True ∧ p5) → True) → p5) ∧ (((p3 ∧ (p4 ∧ p5)) ∨ False) ∨ (True ∧ ((p3 → p1) ∨ ((p2 ∧ (True ∨ p3)) ∧ (p4 ∧ p4)))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((True ∧ p5) → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h20.left
        let h25 := h20.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : ((True ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h26
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h20.left
        let h31 := h20.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h32 : ((True ∧ p5) → True) := by
          -- Implications on the right can always be decomposed.
          intro h33
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h34 := h2 h32
        -- One of the premise coincides with the conclusion.
        exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618439361454509854164982205073 : (((((((True ∧ True) ∨ p4) ∨ p3) → (p2 ∧ (p5 ∨ (((True → p5) ∨ p1) ∨ (p4 → (False ∨ ((p2 ∨ p1) ∨ (p3 ∨ p5)))))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



